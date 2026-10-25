///@ts-check
/**
 * Injects jsCoq into the SF terse slide decks. Derived from
 * frontend/classic/js/jscoq-agent.js with the fixes accumulated while
 * porting to Rocq 9 / jsCoq 1.99 (see Lecture-planning.md §9):
 *
 *  - imports the built bundle (the raw module tree 404s in a browser);
 *    version-stamped so rebuilt bundles are never shadowed by module cache
 *  - content_type 'plain': the CoqManager default is 'markdown', which makes
 *    the document URI *.mv and Fleche then blanks everything outside ```coq
 *    fences — i.e. the entire coqdoc-extracted document
 *  - node_modules_path: deck pages live under /terse/, so the affiliate
 *    probe must not resolve node_modules against the page URL
 *  - extra Deprettify rules incl. ∀ (coqdoc emits it; without the reverse
 *    mapping the lexer dies with "Undefined token")
 *  - readiness-proof boot (a module can finish loading after
 *    DOMContentLoaded already fired)
 *  - Alt-Down on a slide starts stepping at that slide's first pane when
 *    the cursor is not already in one of its panes;
 *  - CodeMirror refresh on slide navigation (editors created while their
 *    slide is hidden render zero-height until refreshed)
 *  - slide realignment after sentence-stepping (Alt-↓/↑): scrollIntoView on
 *    the owning slide marker; hash synced via replaceState (a real hash jump
 *    steals focus), and no CM refresh afterwards (it would scroll the cursor
 *    back into view, undoing the snap)
 */
import { JsCoq, Deprettify } from './dist/frontend/index.js?v=sfrepl2';

function jsCoqInject() {
    var b = document.body;
    b.setAttribute('id', 'ide-wrapper');
    b.classList.add('toggled');
    b.classList.add(isTerse() ? 'terse' : 'full');

    var plug = document.createElement('div');
    plug.setAttribute('id', 'jscoq-plug');
    plug.addEventListener('click', jsCoqStart);
    b.append(plug);
}

// Panel visibility: shown unless ?jscoq=off or the user hid it last time.
// localStorage is read defensively: some private/strict-privacy modes throw
// on access, and an uncaught throw here would abort the whole module.
function storedShow() {
    try { return localStorage.jsCoqShow; } catch (e) { return undefined; }
}
var jsCoqShow = location.search === '?jscoq=on' ||
                location.search !== '?jscoq=off' && storedShow() !== 'false';

// QC pages preload the pure-QuickChick stack instead of lf/plf: .vo-load
// Requires bypass the FailedRequire auto-load path (and that round-trip
// is racy anyway), so whatever a page's Requires reach must be preloaded.
var isQCPage = /\/(qc|qc-terse)\//.test(location.pathname);
var sfInitPkgs = isQCPage ? ['init', 'stdlib', 'ltac2', 'quickchick', 'qc']
                          : ['init', 'stdlib', 'ltac2', 'lf', 'plf'];

var jscoq_ids  = ['#main > div.code, #main > div.HIDEFROMHTML > div.code'];
var jscoq_opts = {
    content_type: 'plain',
    layout:    'flex',
    show:      jsCoqShow,
    focus:     false,
    replace:   true,
    editor:    { mode: { 'company-coq': true }, className: 'jscoq code-tight' },
    // stdlib and ltac2 must be preloaded: LF's .vo files need Stdlib.* during
    // vo processing, which does NOT go through the FailedRequire auto-load
    // path (that only reacts to failed Require *sentences* in the document).
    // 'lf'/'plf' preloaded too: the FailedRequire auto-load round-trip
    // (fail -> fetch -> re-create doc -> recheck) proved racy in-browser.
    init_pkgs: sfInitPkgs,
    all_pkgs:  { '+': ['coq', 'software-foundations'] },
    node_modules_path: '../node_modules/',
    init_import: ['utf8'],
    implicit_libs: true
};

async function jsCoqLoad() {
    // - remove empty code fragments (coqdoc generates some spurious ones)
    for (let code of document.querySelectorAll('#main > div.code')) {
        if (code.textContent?.match(/^\s*$/)) code.remove();
    }

    // - make page div focusable so that keyboard scrolling works
    var page = /** @type {HTMLElement} */ (document.querySelector('#page'));
    page.setAttribute('tabindex', '-1');
    page.focus();

    Deprettify.REPLACES.push(...Deprettify.SF_REPLACES);

    var coq = await JsCoq.start(jscoq_ids, jscoq_opts);
    //@ts-ignore
    window.coq = coq;

    // CodeMirror instances created while their slide is hidden render
    // zero-height until refresh()ed; slides.js navigates via location.hash.
    var refreshCM = () => setTimeout(() =>
        document.querySelectorAll('.CodeMirror').forEach(e =>
            /** @type {any} */(e).CodeMirror?.refresh()), 60);
    window.addEventListener('hashchange', refreshCM);
    refreshCM();

    // Keep slide alignment when sentence-stepping crosses into a new slide.
    function alignSlideToCursor() {
        var any = document.querySelectorAll('.slide')[1];
        if (!any || !any.style.marginTop || any.style.marginTop === '0px')
            return;                       // not in slide mode
        var el = document.activeElement && document.activeElement.closest
                 && document.activeElement.closest('.CodeMirror');
        if (!el) return;
        var last = null;                  // markers are nested in div.doc
        document.querySelectorAll('.slide').forEach(function (m) {
            if (m.compareDocumentPosition(el) & Node.DOCUMENT_POSITION_FOLLOWING)
                last = m;
        });
        if (!last) return;
        if (location.hash !== '#' + last.id)
            history.replaceState(null, '', '#' + last.id);
        last.scrollIntoView({ block: 'start' });
    }
    // Slide marker (div.slide from slides.js) that owns an element.
    function slideOf(el) {
        var last = null;
        document.querySelectorAll('.slide').forEach(function (m) {
            if (m.compareDocumentPosition(el) & Node.DOCUMENT_POSITION_FOLLOWING)
                last = m;
        });
        return last;
    }
    // The slide on screen: the last marker at or above the top of the
    // scrolling container (div#page; slides.js scrolls it via the hash).
    function currentSlide() {
        var box = document.getElementById('page') || document.scrollingElement;
        var top = box.getBoundingClientRect().top + 2, last = null;
        document.querySelectorAll('.slide').forEach(function (m) {
            if (m.getBoundingClientRect().top <= top) last = m;
        });
        return last;
    }
    // Alt-Down on a slide whose panes do not hold the cursor: start
    // stepping at that slide's first pane instead of wherever the cursor was.
    function enterSlideProof() {
        var ed = coq.editor, snippets = ed && ed.snippets;
        if (!snippets || !snippets.length) return;
        var cur = currentSlide();
        if (!cur) return;
        var focused = snippets.find(sp => sp.editor.hasFocus());
        if (focused && slideOf(focused.editor.getWrapperElement()) === cur) return;
        var off = 0;
        for (var sp of snippets) {
            // Hidden panes (collapsed proofs) cannot take focus; skip them.
            if (slideOf(sp.editor.getWrapperElement()) === cur && !sp.isHidden()) {
                ed.setCursorOffset(off);
                return;
            }
            off += sp.editor.getValue().length + 1;
        }
    }
    if (coq.goSentence) {
        var _go = coq.goSentence.bind(coq);
        coq.goSentence = (dir) => {
            if (dir > 0) enterSlideProof();
            _go(dir);
            setTimeout(alignSlideToCursor, 140);
        };
    }

    window.addEventListener('beforeunload', () => {
        try { localStorage.jsCoqShow = coq.layout.isVisible(); } catch (e) {}
    });
}

function jsCoqStart() {
    //@ts-ignore
    window.coq.layout.show();
}

/** SF-style terse mode */
function isTerse() {
    return !!document.querySelector('[src$="/slides.js"]');
}

function jsCoqBoot() {
    jsCoqInject();
    jsCoqLoad().catch(e => console.error('[jscoq-agent-sf] load failed:', e));
}

if (location.search !== '?jscoq=no') {
    // A module's import graph may finish loading after DOMContentLoaded has
    // already fired, in which case a listener registered there never runs.
    if (document.readyState === 'loading')
        window.addEventListener('DOMContentLoaded', jsCoqBoot);
    else
        jsCoqBoot();
}
