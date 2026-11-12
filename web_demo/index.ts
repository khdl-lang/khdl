import {Compartment, EditorState, Extension} from "@codemirror/state"
import {EditorView, highlightActiveLineGutter, keymap, lineNumbers} from "@codemirror/view"
import {defaultKeymap, history, historyKeymap, indentWithTab, insertNewlineKeepIndent} from "@codemirror/commands"
import {
    bracketMatching,
    defaultHighlightStyle,
    defineLanguageFacet,
    indentUnit,
    Language,
    languageDataProp,
    LanguageSupport,
    StreamLanguage,
    syntaxHighlighting
} from "@codemirror/language"
import {Input, NodeSet, NodeType, Parser, PartialParse, Tree} from "@lezer/common"
import {styleTags, tags} from "@lezer/highlight"
import {oneDark} from "@codemirror/theme-one-dark";
import {diff} from "@codemirror/merge";
import * as khdl_wasm from "khdl_wasm";
import {verilog as mode_verilog} from "@codemirror/legacy-modes/mode/verilog";

import AnsiToHtmlClass from "ansi-to-html";
import Cookies from "js-cookie";
import pako from "pako";
import type {CompileRequest, CompileResponse, CompileResult, WorkerRequest} from "./worker_protocol";
import {wasm_module} from "./wasm_module";
import {new_slot_id, slot_title, SlotStore, STORAGE_KEY} from "./slots";

function build_node_types() {
    const node_types_string = khdl_wasm.codemirror_node_types();

    // build node types
    const child_node_types = node_types_string.map((name, index) => {
        return NodeType.define({id: index, name: name, top: false})
    })
    const top_node_type = NodeType.define({
        id: child_node_types.length, name: "top", top: true, props: [[
            languageDataProp,
            defineLanguageFacet({
                commentTokens: {line: "//", block: {start: "/*", end: "*/"}}
            }),
        ]]
    })
    let all_node_types = child_node_types.concat([top_node_type]);

    // create set, including styles
    const style_tags_object: any = {};
    const tags_any: any = tags;
    for (const name of khdl_wasm.codemirror_node_types()) {
        style_tags_object[name] = tags_any[name];
    }
    const node_set = new NodeSet(all_node_types).extend(styleTags(style_tags_object));

    return {node_set, top_node_type};
}

const {node_set: NODE_SET, top_node_type: TOP_NODE_TYPE} = build_node_types();

// CodeMirror supports incremental parsing.
// We only have a batch parser implemented in Rust though, so we also do a full parse here.
//
// Implementation based on
// https://thetrevorharmon.com/blog/connecting-antlr-to-code-mirror-6-connecting-a-language-server/
class KhdlParser extends Parser {
    createParse(input: Input): PartialParse {
        return this.startParse(input)
    }

    startParse(input: Input | string): PartialParse {
        const input_str = typeof input === "string" ? input : input.read(0, input.length);
        let input_length = input_str.length;

        const tree = Tree.build({
            buffer: Array.from(khdl_wasm.codemirror_tokenize_to_tree(input_str)),
            nodeSet: NODE_SET,
            topID: TOP_NODE_TYPE.id,
        });

        return {
            stoppedAt: input_length,
            parsedPos: input_length,
            stopAt: (_) => {
            },
            advance: () => tree,
        };
    }
}

let language = new Language(null, new KhdlParser(), [], "KHDL");

const element_editor_input = document.getElementById("div-editor-input");
const element_editor_output_verilog = document.getElementById("div-editor-output-verilog");
const element_editor_output_format = document.getElementById("div-editor-output-format");
const element_editor_output_ir = document.getElementById("div-editor-output-ir");
const element_diags_compile = document.getElementById("div-diags-compile");
const element_diags_format = document.getElementById("div-diags-format");
const element_share_link = document.getElementById("button-share") as HTMLAnchorElement;
const element_share_label = document.getElementById("share-label");
const element_tabs = document.getElementById("div-tabs");
const element_new_tab_button = document.getElementById("button-new-tab");
const element_format_button = document.getElementById("button-format");

const ansi_to_html_light = new AnsiToHtmlClass();
const ansi_to_html_dark = new AnsiToHtmlClass({
    colors: {
        0: "#808080",
        1: "#f14c4c",
        2: "#23d18b",
        3: "#f5f543",
        4: "#3b8eea",
        5: "#d670d6",
        6: "#29b8db",
        7: "#e5e5e5",
        8: "#a0a0a0",
        9: "#ff6b6b",
        10: "#5af78e",
        11: "#ffff7a",
        12: "#6cb6ff",
        13: "#ff92df",
        14: "#7ee0f5",
        15: "#ffffff",
    }
});

const dark_mode_query = window.matchMedia("(prefers-color-scheme: dark)");

function escapeHtml(raw: string): string {
    return raw
        .replace(/&/g, "&amp;")
        .replace(/</g, "&lt;")
        .replace(/>/g, "&gt;")
        .replace(/"/g, "&quot;")
        .replace(/'/g, "&#039;");
}

function diagnostics_ansi_to_html(ansi: string): string {
    if (ansi.length == 0) {
        return "";
    }

    const ansi_to_html = dark_mode_query.matches ? ansi_to_html_dark : ansi_to_html_light;
    let result = "";
    for (let line of ansi.split("\n")) {
        if (line.length == 0) {
            result += "<div>&ZeroWidthSpace;</div>";
        } else {
            result += "<div>" + ansi_to_html.toHtml(escapeHtml(line).replaceAll(" ", "&nbsp;")) + "</div>";
        }
    }
    return result;
}

const EMPTY_DOC = "/* empty */";
// The demo used to keep a single source in this cookie, it's moved into the first save slot.
const COOKIE_SOURCE = "source";

let compile_worker: Worker | null = null;
let compile_running = false;

function request_compile(request: CompileRequest) {
    if (compile_running) {
        stop_compile_worker();
    }

    if (compile_worker === null) {
        const worker = new Worker(new URL("./compile_worker.ts", import.meta.url), {type: "module"});
        worker.onmessage = (event: MessageEvent<CompileResponse>) => {
            if (worker === compile_worker) {
                handle_compile_response(event.data);
            }
        };
        worker.onerror = (event) => {
            if (worker === compile_worker) {
                handle_compile_response({type: "error", message: event.message || "compile worker failed"});
            }
        };
        compile_worker = worker;
        worker.postMessage({type: "init", module: wasm_module} satisfies WorkerRequest);
    }

    compile_running = true;
    compile_worker.postMessage({type: "compile", request} satisfies WorkerRequest);
}

function stop_compile_worker() {
    compile_worker?.terminate();
    compile_worker = null;
    compile_running = false;
}

function handle_compile_response(response: CompileResponse) {
    compile_running = false;
    if (response.type === "result") {
        apply_compile_result(response.result);
    } else {
        // the wasm instance might be in a broken state after a panic, start a new worker for the next compile
        stop_compile_worker();
        apply_compile_result({
            compile_diags_ansi: `compiler panicked\nsee console for the stack trace\n${response.message}`,
            compile_prints: [],
            lowered_verilog: "",
            format_diags_ansi: `compiler panicked\n${response.message}`,
            format_debug_str: "",
            ir_debug_str: "",
        });
    }
}

function apply_compile_result(result: CompileResult) {
    let lowered_verilog = result.lowered_verilog;
    let format_debug_str = result.format_debug_str;
    let ir_debug_str = result.ir_debug_str;

    if (result.compile_prints.length > 0) {
        let combined_prints = "// prints:\n";
        for (const print of result.compile_prints) {
            if (combined_prints.endsWith("\n")) {
                combined_prints += "//  ";
            }
            combined_prints += print;
        }
        combined_prints += "\n";
        lowered_verilog = combined_prints + lowered_verilog;
    }

    // display diagnostics as html
    element_diags_compile.innerHTML = diagnostics_ansi_to_html(result.compile_diags_ansi);
    element_diags_format.innerHTML = diagnostics_ansi_to_html(result.format_diags_ansi);

    // replace output contents with newly generated source,
    // put at least some text to prevent confusion
    if (lowered_verilog.length == 0) {
        lowered_verilog = EMPTY_DOC;
    }
    if (format_debug_str.length == 0) {
        format_debug_str = EMPTY_DOC;
    }
    if (ir_debug_str.length == 0) {
        ir_debug_str = EMPTY_DOC;
    }

    editor_view_output_verilog.dispatch({
        changes: {
            from: 0,
            to: editor_view_output_verilog.state.doc.length,
            insert: lowered_verilog,
        }
    })
    editor_view_output_format.dispatch({
        changes: {
            from: 0,
            to: editor_view_output_format.state.doc.length,
            insert: format_debug_str,
        }
    })
    editor_view_output_ir.dispatch({
        changes: {
            from: 0,
            to: editor_view_output_ir.state.doc.length,
            insert: ir_debug_str,
        }
    })
}

function onDocumentChanged(source: string, format_visible: boolean, ir_visible: boolean) {
    // store code in the save slot of the current tab
    if (slots.get(active_slot_id)?.source !== source) {
        slots.set_source(active_slot_id, source);
        render_tabs();
    }

    // store code in share link, as the parameter "source", compressed and base64 encoded
    // https://developer.mozilla.org/en-US/docs/Glossary/Base64#the_unicode_problem
    const url = new URL(window.location.href);
    url.searchParams.set("source", "cb64-" + btoa(String.fromCharCode.apply(null, pako.deflate(source))));
    element_share_link.href = url.toString()

    request_compile({source, include_format: format_visible, include_ir: ir_visible});
}

function color_scheme_extension(): Extension {
    if (dark_mode_query.matches) {
        return oneDark;
    } else {
        return syntaxHighlighting(defaultHighlightStyle);
    }
}

const color_scheme_compartment = new Compartment();

function common_extensions(): Extension[] {
    return [
        keymap.of([{key: "Enter", run: insertNewlineKeepIndent}]),
        keymap.of([indentWithTab]),
        keymap.of(defaultKeymap),
        keymap.of(historyKeymap),
        history(),

        lineNumbers(),
        bracketMatching(),

        indentUnit.of(" ".repeat(4)),
        color_scheme_compartment.of(color_scheme_extension()),
    ];
}

function formatCurrentCode() {
    const currentCode = editor_view_input.state.doc.toString();
    const formatted = khdl_wasm.format_source(currentCode);
    if (formatted !== undefined) {
        // set input through diff to try to preserve the cursor position
        const changes = diff(currentCode, formatted).map(change => ({
            from: change.fromA,
            to: change.toA,
            insert: formatted.slice(change.fromB, change.toB),
        }));
        editor_view_input.dispatch({
            changes,
            userEvent: "format",
        });
    }
}

// TODO compare legacy mode to to https://www.npmjs.com/package/codemirror-lang-verilog
let editor_state_output_verilog = EditorState.create({
    doc: EMPTY_DOC,
    extensions: common_extensions().concat([
        EditorState.readOnly.of(true),
        StreamLanguage.define(mode_verilog)
    ]),
})
let editor_view_output_verilog = new EditorView({
    state: editor_state_output_verilog,
    parent: element_editor_output_verilog
})
let editor_state_output_format = EditorState.create({
    doc: EMPTY_DOC,
    extensions: common_extensions().concat([
        EditorState.readOnly.of(true),
        new LanguageSupport(language)
    ]),
})
let editor_view_output_format = new EditorView({
    state: editor_state_output_format,
    parent: element_editor_output_format
})
let editor_state_output_ir = EditorState.create({
    doc: EMPTY_DOC,
    extensions: common_extensions().concat([
        EditorState.readOnly.of(true),
    ]),
})
let editor_view_output_ir = new EditorView({
    state: editor_state_output_ir,
    parent: element_editor_output_ir
})

let format_visible = false;
let ir_visible = false;

function force_update() {
    onDocumentChanged(editor_view_input.state.doc.toString(), format_visible, ir_visible);
}

let updateListenerExtension = EditorView.updateListener.of((update) => {
    if (update.docChanged) {
        onDocumentChanged(editor_view_input.state.doc.toString(), format_visible, ir_visible);
    }
})

const wasm_initial_source = khdl_wasm.initial_source();

// Each tab of the editor is a save slot.
const slots = new SlotStore(() => {
    const id = new_slot_id();
    return {slots: [{id, source: Cookies.get(COOKIE_SOURCE) ?? wasm_initial_source}], active: id};
});
Cookies.remove(COOKIE_SOURCE);

// Open the code of a share link in its own tab, so it doesn't overwrite anything.
{
    const url = new URL(window.location.href);
    const source = url.searchParams.get("source");
    if (source != null) {
        if (source.startsWith("cb64-")) {
            try {
                slots.open_source(pako.inflate(Uint8Array.from(atob(source.slice(5)), c => c.charCodeAt(0)), {to: "string"}));
            } catch (e) {
                console.error("Failed to decode shared source", e);
            }
        }
        // remove the code from the address bar, so reloading the page doesn't open it again
        url.searchParams.delete("source");
        window.history.replaceState(null, "", url);
    }
}

let active_slot_id = slots.active.id;

function create_input_state(source: string): EditorState {
    return EditorState.create({
        doc: source,
        extensions: common_extensions().concat([
            highlightActiveLineGutter(),
            new LanguageSupport(language),
            updateListenerExtension,
            keymap.of([{
                key: "Ctrl-Shift-i", run: () => {
                    formatCurrentCode();
                    return true;
                }
            }]),
        ])
    });
}

// Editor states of the tabs visited in this page, to keep their undo history.
const input_states = new Map<string, EditorState>();

let editor_view_input = new EditorView({
    state: create_input_state(slots.active.source),
    parent: element_editor_input,
})

function switch_to_slot(id: string) {
    slots.reload();
    const slot = slots.get(id);
    if (slot === undefined) {
        return;
    }
    if (slots.get(active_slot_id) !== undefined) {
        input_states.set(active_slot_id, editor_view_input.state);
    }

    // reuse the state from an earlier visit, unless the code was changed in another page since then
    const cached = input_states.get(id);
    const state = cached !== undefined && cached.doc.toString() === slot.source ? cached : create_input_state(slot.source);
    active_slot_id = id;
    slots.set_active(id);
    editor_view_input.setState(state);
    editor_view_input.dispatch({effects: color_scheme_compartment.reconfigure(color_scheme_extension())});
    render_tabs();
    force_update();
}

function close_slot(id: string) {
    slots.reload();
    const slot = slots.get(id);
    if (slot === undefined) {
        return;
    }
    const source = id === active_slot_id ? editor_view_input.state.doc.toString() : slot.source;
    const unchanged = source === wasm_initial_source || source.trim() === "";
    if (!unchanged && !window.confirm(`Close ${slot_title(source)}? Its code will be removed from this browser.`)) {
        return;
    }

    const index = slots.slots.findIndex(slot => slot.id === id);
    slots.remove(id, wasm_initial_source);
    input_states.delete(id);
    if (id === active_slot_id) {
        switch_to_slot(slots.slots[Math.min(index, slots.slots.length - 1)].id);
    } else {
        render_tabs();
    }
}

let rendered_tabs = "";

function render_tabs() {
    const items = slots.slots.map(slot => {
        const source = slot.id === active_slot_id ? editor_view_input.state.doc.toString() : slot.source;
        return {id: slot.id, title: slot_title(source)};
    });

    // only rebuild when something changed, this runs on every edit
    const signature = JSON.stringify([active_slot_id, items]);
    if (signature === rendered_tabs) {
        return;
    }
    rendered_tabs = signature;

    element_tabs.replaceChildren(...items.map(item => {
        const tab = document.createElement("div");
        tab.className = item.id === active_slot_id ? "tab active" : "tab";

        const select = document.createElement("button");
        select.className = "tab-select";
        select.textContent = item.title;
        select.addEventListener("click", () => switch_to_slot(item.id));

        const close = document.createElement("button");
        close.className = "tab-close";
        close.textContent = "\u00d7";
        close.title = "Close tab";
        close.setAttribute("aria-label", `Close ${item.title}`);
        close.addEventListener("click", () => close_slot(item.id));

        tab.append(select, close);
        return tab;
    }));
    element_tabs.querySelector(".tab.active")?.scrollIntoView({block: "nearest", inline: "nearest"});
}

element_new_tab_button.addEventListener("click", () => {
    const id = new_slot_id();
    slots.update(state => {
        state.slots.push({id, source: wasm_initial_source});
    });
    switch_to_slot(id);
});

// keep the tabs in sync with other open demo pages
window.addEventListener("storage", (event) => {
    if (event.key !== null && event.key !== STORAGE_KEY) {
        return;
    }
    slots.reload();
    if (slots.get(active_slot_id) === undefined) {
        // the current tab was closed in another page
        switch_to_slot(slots.active.id);
    } else {
        render_tabs();
    }
});

element_format_button.addEventListener("click", () => formatCurrentCode());

// copy the share link instead of navigating to it
let share_label_timeout: number | undefined = undefined;
element_share_link.addEventListener("click", async (event) => {
    event.preventDefault();
    let label = "Link copied";
    try {
        await navigator.clipboard.writeText(element_share_link.href);
    } catch {
        window.prompt("Copy this link to share the code:", element_share_link.href);
        label = "Share";
    }
    element_share_label.textContent = label;
    window.clearTimeout(share_label_timeout);
    share_label_timeout = window.setTimeout(() => element_share_label.textContent = "Share", 2000);
});

render_tabs();

// add tab change event handlers
function show_output_tab(tab: string) {
    function set_element_display(id: string, filter: string[]) {
        const element = document.getElementById(id);
        if (element) {
            element.style.display = filter.includes(tab) ? 'block' : 'none';
        }
    }

    set_element_display("div-diags-compile", ["verilog", "ir"])
    set_element_display("div-editor-output-verilog", ["verilog"])

    set_element_display("div-diags-format", ["format"])
    set_element_display("div-editor-output-format", ["format"])

    set_element_display("div-editor-output-ir", ["ir"])

    document.querySelectorAll<HTMLButtonElement>(".output-tab").forEach(button => {
        button.classList.toggle("active", button.dataset.output == tab);
    });

    // update optional tab states and possibly recompute if one of them was not visible before
    let format_was_visible = format_visible;
    let ir_was_visible = ir_visible;
    format_visible = (tab == "format");
    ir_visible = (tab == "ir");
    if ((format_visible && !format_was_visible) || (ir_visible && !ir_was_visible)) {
        force_update();
    }
}

document.querySelectorAll<HTMLButtonElement>(".output-tab").forEach(button => {
    button.addEventListener("click", () => show_output_tab(button.dataset.output));
});

// react to light/dark mode changes
dark_mode_query.addEventListener("change", () => {
    const effects = color_scheme_compartment.reconfigure(color_scheme_extension());
    for (const view of [editor_view_input, editor_view_output_verilog, editor_view_output_format, editor_view_output_ir]) {
        view.dispatch({effects});
    }
    force_update();
});

// initial update
force_update();
