#pragma once

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "preprocessor/macro_table.h"

#include <functional>
#include <string>
#include <string_view>
#include <vector>

namespace delta {

using FileResolver = std::function<std::string(std::string_view)>;

struct PreprocConfig {
    std::vector<std::string> include_dirs;
    std::vector<std::pair<std::string, std::string>> defines;
};

class Preprocessor {
public:
    Preprocessor(SourceManager& src_mgr, DiagEngine& diag, PreprocConfig config);

    std::string preprocess(uint32_t file_id);

    const MacroTable& macro_table() const { return macros_; }

private:
    std::string process_source(std::string_view src, uint32_t file_id, int depth);
    bool process_directive(
        std::string_view line, uint32_t file_id, uint32_t line_num, int depth, std::string& output);
    bool is_active() const;
    void handle_define(std::string_view rest, SourceLoc loc);
    void handle_undef(std::string_view rest, SourceLoc loc);
    void handle_ifdef(std::string_view rest, bool inverted);
    void handle_else();
    void handle_endif();
    void handle_include(std::string_view filename, SourceLoc loc, int depth, std::string& output);
    std::string expand_macro(const MacroDef& macro, std::string_view args_text);
    std::string resolve_include(std::string_view filename);

    SourceManager& src_mgr_;
    DiagEngine& diag_;
    PreprocConfig config_;
    MacroTable macros_;
    std::vector<bool> cond_stack_;
    int include_depth_ = 0;
    static constexpr int kMaxIncludeDepth = 15;
};

} // namespace delta
