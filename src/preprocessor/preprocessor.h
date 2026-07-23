#pragma once

#include <functional>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "lexer/keywords.h"
#include "preprocessor/macro_table.h"

namespace delta {

using FileResolver = std::function<std::string(std::string_view)>;

struct PreprocConfig {
  std::vector<std::string> include_dirs;
  std::vector<std::pair<std::string, std::string>> defines;
};

struct CondState {
  bool active;
  bool any_taken;
  bool parent_active;
};

class Preprocessor {
 public:
  Preprocessor(SourceManager& src_mgr, DiagEngine& diag, PreprocConfig config);

  std::string Preprocess(uint32_t file_id);
  // §22.14 pairs `begin_keywords with a later `end_keywords, and the region
  // between them is allowed to run past the end of a source file. A region is
  // therefore only known to be unterminated once every source file has been
  // preprocessed, which is why this is a separate call the driver makes after
  // its last Preprocess() rather than something Preprocess() does on its own.
  void ReportUnterminatedKeywordRegions();
  static std::string_view Trim(std::string_view s);

 private:
  std::string ProcessSource(std::string_view src, uint32_t file_id, int depth);
  bool ProcessDirective(std::string_view line, uint32_t file_id,
                        uint32_t line_num, int depth, std::string& output);
  bool ProcessConditionalDirective(std::string_view line, uint32_t file_id,
                                   uint32_t line_num, std::string& output);
  bool ProcessStateDirective(std::string_view line, SourceLoc loc, int depth,
                             std::string& output);
  void OutputRemainder(std::string_view line, std::string_view directive,
                       uint32_t file_id, uint32_t line_num,
                       std::string& output);
  // Emits the text after a directive that has no newline-terminated end (22.2),
  // first dispatching it as a directive so a same-line trailing directive (e.g.
  // `celldefine `timescale ...) is still acted on.
  void ProcessDirectiveRemainder(std::string_view line,
                                 std::string_view directive, SourceLoc loc,
                                 int depth, std::string& output);
  // True when an inline `ifdef…`endif resolves entirely on this line (22.6).
  bool HasInlineConditional(std::string_view line) const;
  void OutputText(std::string_view text, uint32_t file_id, uint32_t line_num,
                  std::string& output);
  void OutputPreExpanded(std::string_view text, std::string& output);
  bool IsActive() const;
  void HandleDefine(std::string_view rest, SourceLoc loc);
  void HandleUndef(std::string_view rest, SourceLoc loc);
  void HandleIfdef(std::string_view rest, bool inverted);
  void HandleElsif(std::string_view rest);
  bool EvalIfdefExpr(std::string_view expr);
  bool EvalIfdefEquiv(std::string_view& expr);
  bool EvalIfdefImpl(std::string_view& expr);
  bool EvalIfdefOr(std::string_view& expr);
  bool EvalIfdefAnd(std::string_view& expr);
  bool EvalIfdefUnary(std::string_view& expr);
  void HandleElse();
  void HandleEndif();
  void HandleInclude(std::string_view filename, SourceLoc loc, int depth,
                     std::string& output, bool angle_bracket);
  void HandleTimescale(std::string_view rest, SourceLoc loc);
  void HandleDefaultNettype(std::string_view rest, SourceLoc loc);
  void HandleUnconnectedDrive(std::string_view rest, SourceLoc loc);
  void HandleLine(std::string_view rest, SourceLoc loc);
  void HandleDefaultDecayTime(std::string_view rest, SourceLoc loc);
  void HandleDefaultTriregStrength(std::string_view rest, SourceLoc loc);
  void HandleBeginKeywords(std::string_view rest, SourceLoc loc,
                           std::string& output);
  void HandleEndKeywords(SourceLoc loc, std::string& output);
  bool TryPredefinedMacro(std::string_view name, std::string& output,
                          uint32_t file_id, uint32_t line_num);
  bool TryExpandMacro(std::string_view trimmed, std::string& output,
                      uint32_t file_id, uint32_t line_num, int depth);
  bool ExpandUserDefinedMacro(std::string_view name,
                              std::string_view macro_name, std::string& output,
                              SourceLoc loc, int depth);
  bool IsRecursiveExpansion(std::string_view name, SourceLoc loc) const;
  bool ExpandFunctionLikeMacro(const MacroDef& def, std::string_view macro_name,
                               SourceLoc loc, std::string& expanded,
                               std::string_view& rest);
  std::string ExpandInlineConditionals(std::string_view line);
  std::string ExpandInlineMacros(std::string_view line, uint32_t file_id,
                                 uint32_t line_num);
  size_t ExpandSingleInlineMacro(std::string_view line, size_t pos,
                                 uint32_t file_id, uint32_t line_num,
                                 std::string& result);
  bool TryExpandInlinePredefined(std::string_view name, uint32_t file_id,
                                 uint32_t line_num, std::string& result);
  size_t ExpandInlineFunctionMacro(const MacroDef& def, std::string_view line,
                                   size_t name_end, SourceLoc loc,
                                   std::string& result);
  void ResolveAndReadInclude(std::string_view fn, SourceLoc loc, int depth,
                             std::string& output, bool angle_bracket);
  std::string ExpandMacro(const MacroDef& macro, std::string_view args_text,
                          SourceLoc loc);
  bool ValidateMacroArgCount(const MacroDef& def, std::string_view args_text,
                             SourceLoc loc, std::string_view name);
  std::string ResolveInclude(std::string_view filename,
                             const std::string& src_dir);
  void DefinePredefined(std::string name, std::string body);
  void TrackDesignElement(std::string_view trimmed);
  void ExpandAndAppendLine(std::string_view line, uint32_t file_id,
                           uint32_t line_num, std::string& output);
  bool ProcessBlockCommentLine(std::string_view line, uint32_t file_id,
                               uint32_t line_num, int depth,
                               std::string& output);
  void SkipBlockCommentLine(std::string_view line, uint32_t file_id,
                            uint32_t line_num, int depth, std::string& output);
  bool RejectInsideDesignElement(std::string_view directive_name,
                                 SourceLoc loc);
  void ResetDirectiveState();
  void HandlePragma(std::string_view rest, SourceLoc loc);
  bool ProcessDelayModeDirective(std::string_view line, SourceLoc loc);
  bool ProcessSimpleStateDirective(std::string_view line, SourceLoc loc,
                                   int depth, std::string& output);
  bool ProcessMiscStateDirective(std::string_view line, SourceLoc loc,
                                 uint32_t file_id, uint32_t line_num,
                                 std::string& output);
  bool ProcessExpandedStateDirective(std::string_view line, SourceLoc loc,
                                     uint32_t file_id, uint32_t line_num,
                                     std::string& output);
  void ProcessIncludeDirective(std::string_view line, SourceLoc loc, int depth,
                               std::string& output);
  bool ProcessActiveOnlyDirective(std::string_view line, SourceLoc loc,
                                  int depth, std::string& output);
  bool ProcessKeywordsDirective(std::string_view line, SourceLoc loc,
                                uint32_t file_id, uint32_t line_num,
                                std::string& output);

  static std::vector<std::string> ParseMacroParams(
      std::string_view params, std::vector<std::string>& defaults);
  static std::string_view ExtractBalancedArgs(std::string_view text);
  static std::vector<std::string_view> SplitMacroArgs(std::string_view args);
  // Given text whose first character is the '(' opening a formal parameter
  // list, returns the index of the matching ')', honoring the matched-pair and
  // escaped-identifier protections of 22.5.1 (so a ')' inside a default value
  // is not read as the end of the list). Returns npos if unbalanced.
  static size_t FindMacroParamListClose(std::string_view text);
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

 public:
  const TimeScale& CurrentTimescale() const { return current_timescale_; }
  TimeUnit GlobalPrecision() const { return global_precision_; }
  bool HasTimescale() const { return has_timescale_; }
  NetType DefaultNetType() const { return default_net_type_; }
  bool InCelldefine() const { return in_celldefine_; }
  const std::vector<std::string>& CellModuleNames() const {
    return cell_module_names_;
  }
  NetType UnconnectedDrive() const { return unconnected_drive_; }
  uint32_t LineOffset() const { return line_offset_; }
  bool HasLineOverride() const { return has_line_override_; }
  const std::string& LineFile() const { return line_file_override_; }

  uint64_t DefaultDecayTime() const { return default_decay_time_; }
  double DefaultDecayTimeReal() const { return default_decay_time_real_; }
  bool DefaultDecayTimeInfinite() const { return default_decay_time_infinite_; }
  uint32_t DefaultTriregStrength() const { return default_trireg_strength_; }
  bool HasDefaultTriregStrength() const { return has_default_trireg_strength_; }
  enum DelayModeDirective DelayModeDirective() const {
    return delay_mode_directive_;
  }

 private:
  TimeScale current_timescale_;
  TimeUnit global_precision_ = TimeUnit::kNs;
  bool has_timescale_ = false;
  NetType default_net_type_ = NetType::kWire;
  bool in_celldefine_ = false;
  NetType unconnected_drive_ = NetType::kWire;
  uint32_t line_offset_ = 0;
  uint32_t line_override_src_line_ = 0;
  bool has_line_override_ = false;
  std::string line_file_override_;
  // One entry per `begin_keywords region still open, innermost last. The
  // opening location rides along so an unterminated region can be blamed on
  // the directive that opened it.
  struct KeywordRegion {
    KeywordVersion version;
    SourceLoc loc;
  };
  std::vector<KeywordRegion> keyword_version_stack_;
  std::vector<std::string> expansion_stack_;
  uint32_t design_element_depth_ = 0;
  std::vector<std::string> cell_module_names_;
  bool in_block_comment_ = false;

  uint64_t default_decay_time_ = 0;
  double default_decay_time_real_ = 0.0;
  bool default_decay_time_infinite_ = true;
  uint32_t default_trireg_strength_ = 0;
  bool has_default_trireg_strength_ = false;
  enum DelayModeDirective delay_mode_directive_ = DelayModeDirective::kNone;
};

bool IsCompilerDirective(std::string_view name);
bool HasUnterminatedString(std::string_view body);
bool IsIdentChar(char c);

}  // namespace delta
