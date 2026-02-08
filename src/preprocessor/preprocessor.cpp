#include "preprocessor/preprocessor.h"

#include <algorithm>
#include <cctype>
#include <fstream>
#include <sstream>

namespace delta {

Preprocessor::Preprocessor(SourceManager& src_mgr, DiagEngine& diag, PreprocConfig config)
    : src_mgr_(src_mgr), diag_(diag), config_(std::move(config)) {
    for (const auto& [name, value] : config_.defines) {
        MacroDef def;
        def.name = name;
        def.body = value;
        macros_.define(std::move(def));
    }
}

std::string Preprocessor::preprocess(uint32_t file_id) {
    auto content = src_mgr_.file_content(file_id);
    return process_source(content, file_id, 0);
}

static std::string_view trim(std::string_view s) {
    while (!s.empty() && std::isspace(static_cast<unsigned char>(s.front()))) {
        s.remove_prefix(1);
    }
    while (!s.empty() && std::isspace(static_cast<unsigned char>(s.back()))) {
        s.remove_suffix(1);
    }
    return s;
}

static bool starts_with_directive(std::string_view line, std::string_view dir) {
    auto trimmed = trim(line);
    if (trimmed.size() < dir.size() + 1) {
        return false;
    }
    if (trimmed[0] != '`') {
        return false;
    }
    return trimmed.substr(1, dir.size()) == dir;
}

static std::string_view after_directive(std::string_view line, std::string_view dir) {
    auto trimmed = trim(line);
    auto rest = trimmed.substr(1 + dir.size());
    return trim(rest);
}

std::string Preprocessor::process_source(std::string_view src, uint32_t file_id, int depth) {
    if (depth > kMaxIncludeDepth) {
        diag_.error({file_id, 1, 1}, "include depth exceeds maximum of 15");
        return "";
    }

    std::string output;
    output.reserve(src.size());
    uint32_t line_num = 0;
    size_t pos = 0;

    while (pos < src.size()) {
        size_t eol = src.find('\n', pos);
        if (eol == std::string_view::npos) {
            eol = src.size();
        }
        std::string_view line = src.substr(pos, eol - pos);
        ++line_num;

        if (!process_directive(line, file_id, line_num, depth, output)) {
            if (is_active()) {
                output.append(line);
            }
        }
        output.push_back('\n');
        pos = eol + 1;
    }
    return output;
}

bool Preprocessor::process_directive(
    std::string_view line, uint32_t file_id, uint32_t line_num, int depth, std::string& output) {
    auto trimmed = trim(line);
    if (trimmed.empty() || trimmed[0] != '`') {
        return false;
    }
    SourceLoc loc = {file_id, line_num, 1};

    if (starts_with_directive(line, "define")) {
        if (is_active()) {
            handle_define(after_directive(line, "define"), loc);
        }
        return true;
    }
    if (starts_with_directive(line, "undef")) {
        if (is_active()) {
            handle_undef(after_directive(line, "undef"), loc);
        }
        return true;
    }
    if (starts_with_directive(line, "ifdef")) {
        handle_ifdef(after_directive(line, "ifdef"), false);
        return true;
    }
    if (starts_with_directive(line, "ifndef")) {
        handle_ifdef(after_directive(line, "ifndef"), true);
        return true;
    }
    if (starts_with_directive(line, "else")) {
        handle_else();
        return true;
    }
    if (starts_with_directive(line, "endif")) {
        handle_endif();
        return true;
    }
    if (starts_with_directive(line, "include") && is_active()) {
        handle_include(after_directive(line, "include"), loc, depth, output);
        return true;
    }
    if (starts_with_directive(line, "timescale")) {
        return true; // consumed, handled later
    }
    if (starts_with_directive(line, "resetall")) {
        macros_.undefine_all();
        return true;
    }
    // Check for macro invocation: `MACRO_NAME
    if (is_active()) {
        auto macro_name = trimmed.substr(1);
        auto space_pos = macro_name.find_first_of(" \t(");
        auto name = (space_pos != std::string_view::npos) ? macro_name.substr(0, space_pos) : macro_name;
        const auto* def = macros_.lookup(name);
        if (def != nullptr) {
            output.append(expand_macro(*def, ""));
            return true;
        }
    }
    return false;
}

bool Preprocessor::is_active() const {
    for (bool active : cond_stack_) {
        if (!active) {
            return false;
        }
    }
    return true;
}

void Preprocessor::handle_define(std::string_view rest, SourceLoc loc) {
    auto space = rest.find_first_of(" \t");
    MacroDef def;
    def.def_loc = loc;
    if (space == std::string_view::npos) {
        def.name = std::string(rest);
    } else {
        def.name = std::string(rest.substr(0, space));
        def.body = std::string(trim(rest.substr(space)));
    }
    macros_.define(std::move(def));
}

void Preprocessor::handle_undef(std::string_view rest, SourceLoc /*loc*/) {
    auto name = trim(rest);
    macros_.undefine(name);
}

void Preprocessor::handle_ifdef(std::string_view rest, bool inverted) {
    auto name = trim(rest);
    bool defined = macros_.is_defined(name);
    cond_stack_.push_back(inverted ? !defined : defined);
}

void Preprocessor::handle_else() {
    if (!cond_stack_.empty()) {
        cond_stack_.back() = !cond_stack_.back();
    }
}

void Preprocessor::handle_endif() {
    if (!cond_stack_.empty()) {
        cond_stack_.pop_back();
    }
}

void Preprocessor::handle_include(
    std::string_view filename_raw, SourceLoc loc, int depth, std::string& output) {
    // Strip quotes: "file.sv" or <file.sv>
    auto fn = trim(filename_raw);
    if (fn.size() >= 2 && (fn.front() == '"' || fn.front() == '<')) {
        fn = fn.substr(1, fn.size() - 2);
    }
    auto resolved = resolve_include(fn);
    if (resolved.empty()) {
        diag_.error(loc, "cannot find include file '" + std::string(fn) + "'");
        return;
    }
    std::ifstream ifs(resolved);
    if (!ifs) {
        diag_.error(loc, "cannot open include file '" + resolved + "'");
        return;
    }
    std::ostringstream ss;
    ss << ifs.rdbuf();
    auto content = ss.str();
    auto inc_id = src_mgr_.add_file(resolved, content);
    output.append(process_source(content, inc_id, depth + 1));
}

std::string Preprocessor::expand_macro(const MacroDef& macro, std::string_view /*args_text*/) {
    return macro.body;
}

std::string Preprocessor::resolve_include(std::string_view filename) {
    for (const auto& dir : config_.include_dirs) {
        auto path = dir + "/" + std::string(filename);
        std::ifstream ifs(path);
        if (ifs.good()) {
            return path;
        }
    }
    return "";
}

} // namespace delta
