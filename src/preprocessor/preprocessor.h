#pragma once

#include <functional>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "preprocessor/macro_table.h"

namespace delta {

using FileResolver = std::function<std::string(std::string_view)>;

struct PreprocConfig {
  std::vector<std::string> include_dirs;
  std::vector<std::pair<std::string, std::string>> defines;
};

struct CondState {
  bool active;         // Is this branch currently active?
  bool any_taken;      // Has any branch in this chain been taken?
  bool parent_active;  // Was enclosing scope active at ifdef entry?
};

class Preprocessor {
 public:
  Preprocessor(SourceManager& src_mgr, DiagEngine& diag, PreprocConfig config);

  std::string Preprocess(uint32_t file_id);

 private:
  std::string ProcessSource(std::string_view src, uint32_t file_id, int depth);
  bool ProcessDirective(std::string_view line, uint32_t file_id,
                        uint32_t line_num, int depth, std::string& output);
  bool ProcessConditionalDirective(std::string_view line);
  bool IsActive() const;
  void HandleDefine(std::string_view rest, SourceLoc loc);
  void HandleUndef(std::string_view rest, SourceLoc loc);
  void HandleIfdef(std::string_view rest, bool inverted);
  void HandleElsif(std::string_view rest);
  void HandleElse();
  void HandleEndif();
  void HandleInclude(std::string_view filename, SourceLoc loc, int depth,
                     std::string& output);
  bool TryExpandMacro(std::string_view trimmed, std::string& output,
                      uint32_t file_id, uint32_t line_num);
  std::string ExpandMacro(const MacroDef& macro, std::string_view args_text);
  std::string ResolveInclude(std::string_view filename);

  static std::vector<std::string> ParseMacroParams(std::string_view params);
  static std::string_view ExtractBalancedArgs(std::string_view text);
  static std::vector<std::string_view> SplitMacroArgs(std::string_view args);
  static std::string SubstituteParams(
      std::string_view body, const std::vector<std::string>& params,
      const std::vector<std::string_view>& args);

  SourceManager& src_mgr_;
  DiagEngine& diag_;
  PreprocConfig config_;
  MacroTable macros_;
  std::vector<CondState> cond_stack_;
  int include_depth_ = 0;
  static constexpr int kMaxIncludeDepth = 15;
};

}  // namespace delta
