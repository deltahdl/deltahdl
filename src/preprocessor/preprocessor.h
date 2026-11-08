#pragma once

#include <cstddef>
#include <cstdint>
#include <functional>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "lexer/keywords.h"
#include "preprocessor/macro_table.h"
#include "preprocessor/protect_digest_block.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_license.h"
#include "preprocessor/protect_viewport.h"

namespace delta {

using FileResolver = std::function<std::string(std::string_view)>;

struct PragmaKeywordExpression {
  std::string_view keyword;
  std::string_view value;
  bool has_value = false;
  std::string_view value_list;
};

struct PragmaReading {
  std::string_view error;
  std::string_view name;
  std::vector<PragmaKeywordExpression> keywords;
  bool block_comment_open = false;
};

PragmaReading ReadPragmaDirective(std::string_view rest);

struct PreprocConfig {
  std::vector<std::string> include_dirs;
  std::vector<std::pair<std::string, std::string>> defines;
  std::string protect_key;
  ProtectKeyList protect_keys;
  ProtectLicenseAsk ask_license;
};

struct ProtectRuntimeLicense {
  ProtectLicense license;
  SourceLoc loc;
};

struct CondState {
  bool active;
  bool any_taken;
  bool parent_active;
  SourceLoc opened = {};
  bool else_seen = false;
};

enum class ProtectBlockKind : std::uint8_t {
  kNone,
  kKey,
  kData,
  kDigest,
};

struct OutputMark {
  size_t output_size = 0;
  size_t origins_size = 0;
};

enum class MacroUsageEnd : std::uint8_t { kComplete, kListOpen, kNameAlone };

struct ActiveLineEmit;

class Preprocessor {
 public:
  Preprocessor(SourceManager& src_mgr, DiagEngine& diag, PreprocConfig config);

  std::string Preprocess(uint32_t file_id);

  const std::vector<OutputLineOrigin>& LineOrigins() const {
    return line_origins_;
  }
  void ReportUnterminatedKeywordRegions();
  void BeginCompilationUnit();
  static std::string_view Trim(std::string_view s);

 private:
  std::string ProcessSource(std::string_view src, uint32_t file_id, int depth);

  void NoteOutputLine(uint32_t file_id, uint32_t line);
  OutputMark MarkOutput(const std::string& output) const;
  void NoteOutputLines(uint32_t file_id, uint32_t line,
                       const std::string& output, OutputMark mark);
  std::string WithoutKeywordMarkers(std::string_view src, uint32_t file_id);

  void TakeLineFileOverrideId();

  bool TookAnnouncedValue(std::string_view line, SourceLoc loc, int depth,
                          std::string& output);
  void ProcessUndefDirective(std::string_view line, SourceLoc loc,
                             std::string& output);
  bool ProcessDirective(std::string_view line, uint32_t file_id,
                        uint32_t line_num, int depth, std::string& output);
  bool ProcessConditionalDirective(std::string_view line, uint32_t file_id,
                                   uint32_t line_num, std::string& output);
  bool ProcessStateDirective(std::string_view line, SourceLoc loc, int depth,
                             std::string& output);
  void OutputRemainder(std::string_view line, std::string_view directive,
                       uint32_t file_id, uint32_t line_num,
                       std::string& output);
  void ProcessDirectiveRemainder(std::string_view line,
                                 std::string_view directive, SourceLoc loc,
                                 int depth, std::string& output);
  bool HasInlineConditional(std::string_view line) const;
  void EmitCommentedActiveLine(std::string_view line,
                               const ActiveLineEmit& emit, std::string& output);
  MacroUsageEnd EndOfMacroUsage(std::string_view text) const;
  void OutputText(std::string_view text, uint32_t file_id, uint32_t line_num,
                  std::string& output);
  void OutputPreExpanded(std::string_view text, std::string& output);
  bool IsActive() const;
  void HandleDefine(std::string_view rest, SourceLoc loc);
  void HandleUndef(std::string_view rest, SourceLoc loc);
  void HandleIfdef(std::string_view rest, bool inverted, SourceLoc loc);
  void HandleElsif(std::string_view rest, SourceLoc loc);
  bool EvalIfdefCondition(std::string_view name, std::string_view directive,
                          SourceLoc loc);
  bool EvalIfdefExpr(std::string_view expr, SourceLoc loc);
  bool EvalIfdefEquiv(std::string_view& expr);
  bool EvalIfdefOr(std::string_view& expr);
  bool EvalIfdefAnd(std::string_view& expr);
  bool EvalIfdefUnary(std::string_view& expr);
  void HandleElse(SourceLoc loc);
  void HandleEndif(SourceLoc loc);
  void ReportUnclosedConditionals();
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
  void RunDirectiveOpenedByMacro(std::string expanded, std::string_view rest,
                                 SourceLoc loc, int depth, std::string& output);
  bool IsRecursiveExpansion(std::string_view name, SourceLoc loc) const;
  bool ExpandFunctionLikeMacro(const MacroDef& def, std::string_view macro_name,
                               SourceLoc loc, std::string& expanded,
                               std::string_view& rest);
  std::string ExpandInlineConditionals(std::string_view line, SourceLoc loc);
  void NoteIgnoredLine(std::string_view line, SourceLoc loc);
  std::string ExpandInlineMacros(std::string_view line, uint32_t file_id,
                                 uint32_t line_num);
  std::string ExpandSubstitutedBody(std::string_view body, uint32_t file_id,
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
                             const std::string& src_dir, bool quoted);
  void DefinePredefined(std::string name, std::string body);
  void ResetAllPragmas();
  void TrackDesignElement(std::string_view trimmed);
  void TrackDesignElementHeader(std::string_view trimmed);
  void ExpandAndAppendLine(std::string_view line, uint32_t file_id,
                           uint32_t line_num, std::string& output);
  bool ProcessBlockCommentLine(std::string_view line, uint32_t file_id,
                               uint32_t line_num, int depth,
                               std::string& output);
  void SkipBlockCommentLine(std::string_view line, uint32_t file_id,
                            uint32_t line_num, int depth, std::string& output);
  bool RejectInsideDesignElement(std::string_view directive_name, SourceLoc loc,
                                 Subclause subclause);
  void ResetDirectiveState();
  void HandlePragma(std::string_view rest, SourceLoc loc);
  void ResetPragma(std::string_view pragma_name);
  void ApplyProtectKeywords(
      const std::vector<PragmaKeywordExpression>& keywords, SourceLoc loc);
  bool ReportDelimiterWrittenWithValue(const PragmaKeywordExpression& expr,
                                       SourceLoc loc);
  void CheckDataKeyname(const PragmaKeywordExpression& expr, SourceLoc loc);
  void CheckDigestKeyname(const PragmaKeywordExpression& expr, SourceLoc loc);
  void CheckKeyKeyname(const PragmaKeywordExpression& expr, SourceLoc loc);
  void CheckKeyDesignation(const PragmaKeywordExpression& expr, SourceLoc loc);
  void CheckDataKeyDesignationValue(std::string_view keyword,
                                    std::string_view value, SourceLoc loc);
  void CheckDigestDesignation(const PragmaKeywordExpression& expr,
                              SourceLoc loc);
  void CheckDigestDesignationValue(std::string_view keyword,
                                   std::string_view value, SourceLoc loc);
  void CheckKeyBlockDesignation(std::string_view keyword,
                                std::string_view value, SourceLoc loc);
  void ApplyKeyBlockKeywords(const PragmaKeywordExpression& expr,
                             SourceLoc loc);
  void ApplyAnnouncedBlockKeywords(const PragmaKeywordExpression& expr);
  void ApplyViewport(const PragmaKeywordExpression& expr, SourceLoc loc);
  void RecordEnvelopeViewports();
  void RecordRegionViewports(SourceLoc closed_at);
  void ApplyLicense(const PragmaKeywordExpression& expr, SourceLoc loc);
  bool RecoveredTextLicensed(std::string_view cleartext, uint32_t block_id);
  bool LicencesOfDirectiveGranted(std::string_view body, uint32_t block_id,
                                  uint32_t line_num, int* sealed_inside);
  bool AskDecryptLicense(const ProtectLicense& license, SourceLoc loc);
  void EndAccumulatedProtectPragmas();
  void ResetAnnouncementsAndRecoveredKeys();
  ProtectBlockKind AnnouncedProtectBlockKind() const;
  bool StartGatheredProtectBlock(std::string_view line, SourceLoc loc);
  void AppendGatheredProtectBlockLine(std::string_view line);
  std::string_view GatheredBlockLine(std::string_view line) const;
  void FinishGatheredProtectBlock(int depth, std::string& output);
  void ReadProtectKeyBlock(std::string_view block, SourceLoc loc, int depth);
  bool TakeDataDecryptKeyValue(std::string_view line, SourceLoc loc);
  bool TakeDigestDecryptKeyValue(std::string_view line, SourceLoc loc);
  void ReadProtectDigestBlock(std::string_view block, SourceLoc loc);
  void ReadProtectDataBlock(std::string_view block, SourceLoc loc, int depth,
                            std::string& output);
  struct RecoveredText {
    std::string cleartext;
    uint32_t block_id;
    int depth;
  };
  std::optional<RecoveredText> recovered_text_;
  void ReadRecoveredText(std::string& output);
  void FinishProtectedReading(int depth, std::string& output);
  bool TakeKeyPublicKeyValue(std::string_view line, SourceLoc loc);
  bool TakeDataPublicKeyValue(std::string_view line, SourceLoc loc);
  bool TakeDigestPublicKeyValue(std::string_view line, SourceLoc loc);
  void CheckDataDesignationAgreement(SourceLoc loc);
  void CheckDigestDesignationAgreement(SourceLoc loc);
  bool ReadEncodedProtectValue(std::string_view text, SourceLoc loc,
                               std::string* bytes);
  void SpendEncodedValueSize();
  std::string_view ProtectKeyInEffect() const;
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
  static size_t FindMacroParamListClose(std::string_view text);
  static std::string SubstituteParams(
      std::string_view body, const std::vector<std::string>& params,
      const std::vector<std::string_view>& args);

  SourceManager& src_mgr_;
  DiagEngine& diag_;
  PreprocConfig config_;
  MacroTable macros_;
  MacroTable initial_macros_;
  std::vector<CondState> cond_stack_;
  int include_depth_ = 0;
  static constexpr int kMaxIncludeDepth = 15;

  std::vector<OutputLineOrigin> line_origins_;
  bool recording_origins_ = false;
  bool reading_key_block_ = false;
  std::unordered_set<std::string> names_carried_by_key_blocks_;
  bool KeynameCarriedByKeyBlock(std::string_view owner, std::string_view name);

 public:
  const TimeScale& CurrentTimescale() const { return current_timescale_; }
  TimeUnit GlobalPrecision() const { return global_precision_; }
  int GlobalPrecisionMagnitude() const { return global_precision_magnitude_; }
  bool HasTimescale() const { return has_timescale_; }
  bool HasGlobalPrecision() const { return has_global_precision_; }
  NetType DefaultNetType() const { return default_net_type_; }
  bool InCelldefine() const { return in_celldefine_; }
  const std::vector<ModuleDirectives>& ModuleDirectivesList() const {
    return module_directives_;
  }
  const std::vector<std::string>& CellModuleNames() const {
    return cell_module_names_;
  }
  NetType UnconnectedDrive() const { return unconnected_drive_; }
  uint32_t LineOffset() const { return line_offset_; }
  bool HasLineOverride() const { return has_line_override_; }
  const std::string& LineFile() const { return line_file_override_; }
  const ProtectEnvelopeState& ProtectEnvelopes() const {
    return protect_envelopes_;
  }
  const ProtectKeywordScope& ProtectKeywords() const {
    return protect_keywords_;
  }
  const std::vector<ProtectViewport>& ProtectViewports() const {
    return protect_viewports_;
  }
  const std::vector<ProtectRuntimeLicense>& RuntimeLicenses() const {
    return runtime_licenses_;
  }
  std::string_view DigestKeyInEffect() const;

  std::string DigestMethodInEffect() const;

  std::string_view DigestDecryptKeyInEffect() const;

  std::string_view DigestBlockKeyInEffect() const;

  ProtectDigestCheck LastDigestBlockCheck() const {
    return last_digest_block_check_;
  }

  ProtectEncoding ProtectEncodingInEffect() const;

  uint64_t DefaultDecayTime() const { return default_decay_time_; }
  double DefaultDecayTimeReal() const { return default_decay_time_real_; }
  bool DefaultDecayTimeIsReal() const { return default_decay_time_is_real_; }
  bool DefaultDecayTimeInfinite() const { return default_decay_time_infinite_; }
  uint32_t DefaultTriregStrength() const { return default_trireg_strength_; }
  bool HasDefaultTriregStrength() const { return has_default_trireg_strength_; }
  enum DelayModeDirective DelayModeDirective() const {
    return delay_mode_directive_;
  }

 private:
  TimeScale current_timescale_;
  TimeUnit global_precision_ = TimeUnit::kNs;
  int global_precision_magnitude_ = 1;
  bool has_timescale_ = false;
  bool has_global_precision_ = false;
  NetType default_net_type_ = NetType::kWire;
  bool in_celldefine_ = false;
  NetType unconnected_drive_ = NetType::kWire;
  uint32_t line_offset_ = 0;
  uint32_t line_override_src_line_ = 0;
  bool has_line_override_ = false;
  std::string line_file_override_;
  uint32_t line_file_override_id_ = 0;
  std::unordered_map<std::string, uint32_t> line_file_override_ids_;
  struct KeywordRegion {
    KeywordVersion version;
    SourceLoc loc;
  };
  std::vector<KeywordRegion> keyword_version_stack_;
  std::vector<std::string> expansion_stack_;
  uint32_t design_element_depth_ = 0;
  bool in_attribute_instance_ = false;
  std::string pending_header_;
  bool ifdef_expr_malformed_ = false;
  std::vector<std::string> cell_module_names_;
  std::vector<ModuleDirectives> module_directives_;
  bool in_block_comment_ = false;
  bool in_triple_string_ = false;
  bool in_continued_string_ = false;
  bool in_ignored_string_ = false;
  ProtectEnvelopeState protect_envelopes_;
  ProtectKeywordScope protect_keywords_;
  std::vector<ProtectViewport> protect_viewports_;
  struct EnclosingViewports {
    std::vector<ProtectViewport> viewports;
    uint32_t envelope_source = 0;
    SourceLoc opened_at;
    uint32_t first_source = 0;
  };
  std::vector<EnclosingViewports> protect_viewport_stack_;
  uint32_t protect_envelope_source_ = 0;
  SourceLoc protect_envelope_opened_at_;
  uint32_t protect_envelope_first_source_ = 0;
  std::vector<ProtectRuntimeLicense> runtime_licenses_;
  size_t decryption_refused_depth_ = 0;
  ProtectKeyDesignations protect_key_designations_;
  ProtectKeyDesignations protect_key_block_designations_;
  ProtectKeyDesignations protect_digest_designations_;
  bool key_public_key_value_next_ = false;
  bool data_public_key_value_next_ = false;
  bool digest_public_key_value_next_ = false;
  bool key_block_value_next_ = false;
  bool data_decrypt_key_value_next_ = false;
  bool digest_decrypt_key_value_next_ = false;
  bool digest_block_value_next_ = false;
  bool data_block_value_next_ = false;
  ProtectBlockKind gathering_block_ = ProtectBlockKind::kNone;
  SourceLoc gathering_block_loc_;
  std::string gathering_block_text_;
  std::string data_decrypt_key_;
  std::string digest_decrypt_key_;
  ProtectDigestTarget digest_target_;
  ProtectDigestCheck last_digest_block_check_ = ProtectDigestCheck::kNotChecked;

  uint64_t default_decay_time_ = 0;
  double default_decay_time_real_ = 0.0;
  bool default_decay_time_infinite_ = true;
  bool default_decay_time_is_real_ = false;
  uint32_t default_trireg_strength_ = 0;
  bool has_default_trireg_strength_ = false;
  enum DelayModeDirective delay_mode_directive_ = DelayModeDirective::kNone;
};

bool IsCompilerDirective(std::string_view name);
bool IsDirectiveOtherThanValue(std::string_view name);
bool HasUnterminatedString(std::string_view body);
bool IsIdentChar(char c);

}  // namespace delta
