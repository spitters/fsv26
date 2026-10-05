// Run a CertiRocq-Wasm module emitted by `peregrine wasm` and decode its result.
//
// Module interface: no imports; exports `main_function`, the global `result`,
// `memory`, and the globals `out_of_mem` / `mem_ptr`. Values use the linear
// memory layout of CertiRocq's C backend: an unboxed constructor is the scalar
// (tag << 1) | 1, a boxed one is a pointer whose fields start at the pointer.
//
// Two result shapes. A `nat` is a chain of boxed `S` cells ending in the
// unboxed `O`, so decoding it is a walk whose length is the number itself. A
// `Uint63.int` is one boxed cell holding the value as a little-endian i64.

async function runModule(url, kind) {
  const bytes = await (await fetch(url)).arrayBuffer();
  const t0 = performance.now();
  const { instance } = await WebAssembly.instantiate(bytes, {});
  const e = instance.exports;
  e.main_function();
  const elapsed = performance.now() - t0;
  if (e.out_of_mem.value !== 0) throw new Error("module ran out of linear memory");
  const mem = new DataView(e.memory.buffer);
  let value;
  if (kind === "int63") {
    value = mem.getBigUint64(e.result.value, true);
  } else {
    let v = e.result.value, n = 0n;
    while ((v & 1) === 0) {
      v = mem.getUint32(v + 4, true);
      n++;
    }
    if (v >> 1 !== 0) throw new Error("result is not a nat (constructor " + (v >> 1) + ")");
    value = n;
  }
  return { value, ms: elapsed, bytes: e.mem_ptr.value };
}

function report(row, text, cls) {
  const out = row.querySelector(".out");
  out.textContent = text;
  out.className = "out " + (cls || "");
}

for (const row of document.querySelectorAll("tr[data-module]")) {
  row.querySelector("button").addEventListener("click", async (ev) => {
    const button = ev.currentTarget;
    button.disabled = true;
    report(row, "running…");
    try {
      const r = await runModule(row.dataset.module + ".wasm", row.dataset.kind);
      const expected = BigInt(row.dataset.expected);
      const ok = r.value === expected;
      report(row,
        `${r.value}${ok ? "" : ` — expected ${expected}`}` +
        ` (${r.ms.toFixed(0)} ms, ${(r.bytes / 1024).toFixed(0)} KiB of heap)`,
        ok ? "ok" : "bad");
    } catch (err) {
      // A deeply recursive module overflows the browser's fixed wasm stack;
      // V8 reports that as a RangeError.
      const stack = err instanceof RangeError || /call stack/i.test(err.message);
      report(row, stack ? "stack overflow — see the note below" : String(err.message), "bad");
    } finally {
      button.disabled = false;
    }
  });
}
