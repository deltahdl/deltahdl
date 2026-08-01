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
#include "preprocessor/protect_digest_block.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_keywords.h"

namespace delta {

using FileResolver = std::function<std::string(std::string_view)>;

// One expression of a `pragma directive's own list: the pragma_keyword that
// names it, and the pragma_value written against it when it has one. A keyword
// standing alone leaves `value` empty, and so does one whose value is a
// parenthesized list of further expressions, because those expressions qualify
// the value rather than saying anything the directive's own list says.
//
// `has_value` records which of the two spellings §22.5.1 gives a pragma
// expression the directive used, which an empty `value` cannot say on its own:
// the parenthesized form leaves nothing there and was still written with a
// value. A keyword whose own definition admits one spelling and not the other
// is read against this rather than against the text of the value.
struct PragmaKeywordExpression {
  std::string_view keyword;
  std::string_view value;
  bool has_value = false;
  // The parenthesized form of a pragma_value, as the directive wrote it and
  // with its parentheses, and empty where the value was written any other way.
  //
  // A keyword whose definition spells its value as a list of further
  // expressions -- §34.5.9.1 spells one that way -- says nothing through
  // `value`, that being the text of a value written as a single token. What
  // such a keyword records is the list, so the list is carried here rather
  // than left to be read off the directive a second time.
  std::string_view value_list;
};

struct PreprocConfig {
  std::vector<std::string> include_dirs;
  std::vector<std::pair<std::string, std::string>> defines;
  // The key the user supplies for envelope decryption (§34.3). A tool that
  // processes SystemVerilog source text recovers the cleartext of every
  // protected region the text carries when it is given the key those regions
  // were encrypted under. Left empty, no key was supplied and the regions stay
  // as they are written.
  std::string protect_key;
  // The keys the user supplies under the names that select them (§34.5.12).
  // Where a protected region states whose keys it was encrypted under and
  // which of them was used, the single key those two names pick out of this
  // list is the one the region is read with, so a user holding several keys
  // need not say which region each belongs to. Left empty, no key was supplied
  // under a name and `protect_key` is what every region is read with.
  ProtectKeyList protect_keys;
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
  void HandlePragma(std::string_view rest, SourceLoc loc, int depth,
                    std::string& output);
  void ApplyProtectKeywords(
      const std::vector<PragmaKeywordExpression>& keywords, SourceLoc loc,
      int depth, std::string& output);
  void CheckDataKeyname(const PragmaKeywordExpression& expr, SourceLoc loc);
  void CheckDigestKeyname(const PragmaKeywordExpression& expr, SourceLoc loc);
  void CheckKeyKeyname(const PragmaKeywordExpression& expr, SourceLoc loc);
  void CheckKeyDesignation(const PragmaKeywordExpression& expr, SourceLoc loc);
  // Holds `value`, written against `keyword`, to what §34.5.23 and §34.5.26
  // require of a designation of a key belonging to the entity that provided
  // the keys a protected region's own keys are under: unique for that entity,
  // and reaching the same key as the other designation of it.
  void CheckKeyBlockDesignation(std::string_view keyword,
                                std::string_view value, SourceLoc loc);
  // What §34.5.23 and §34.5.26 have one protect pragma expression do to the
  // reading of those keys: a designation written against a keyword is held to
  // both requirements, and the keyword announcing a public key leaves the line
  // after it to be read as that key's encoded value.
  void ApplyKeyBlockKeywords(const PragmaKeywordExpression& expr,
                             SourceLoc loc);
  // What §34.5.27 and §34.5.14 have one protect pragma expression do to the
  // reading of a protected region. Each of the two keywords, written in the
  // spelling its own subclause defines, speaks for the line after it rather
  // than for its own: one says a key block begins there, and the other says the
  // encoded value of the key opening the region's data block is written there.
  void ApplyAnnouncedBlockKeywords(const PragmaKeywordExpression& expr);
  // Takes `line` as the key block announced by a key_block expression on the
  // line before it, and says whether it did. A line taken this way is key
  // material of the protected block above it rather than text of the design, so
  // the caller neither dispatches it as a directive nor emits it.
  bool TakeKeyBlockValue(std::string_view line, SourceLoc loc, int depth);
  // The same, for the encoded value a data_decrypt_key expression on the line
  // before it announced.
  bool TakeDataDecryptKeyValue(std::string_view line, SourceLoc loc);
  // The same, for the encoded value a digest_decrypt_key expression on the line
  // before it announced (§34.5.20): the key that opens the region's digests.
  bool TakeDigestDecryptKeyValue(std::string_view line, SourceLoc loc);
  // Takes `line` as the digest block announced by a digest_block expression on
  // the line before it, and says whether it did. §34.5.22 has that digest
  // checked against the block it follows, so a line taken this way
  // authenticates what the reading last recovered rather than adding anything
  // to the design, and the caller neither dispatches it as a directive nor
  // emits it.
  bool TakeDigestBlockValue(std::string_view line, SourceLoc loc);
  // Takes `line` as the encoded value announced by a key_public_key expression
  // on the line before it, and says whether it did. A line taken this way is
  // the designation of a key rather than text of the design, so the caller
  // neither dispatches it as a directive nor emits it.
  bool TakeKeyPublicKeyValue(std::string_view line, SourceLoc loc);
  // Reads one encoded value of a protected envelope out of the coding scheme
  // in effect where it stands, leaving what it stands for in `*bytes` and
  // saying whether it could be read at all. §34.5.9 governs every such value
  // alike -- the block carrying a region's data and the value written beneath
  // a keyword that announces a key -- so both are read through here and a
  // reader is told the same thing about either.
  bool ReadEncodedProtectValue(std::string_view text, SourceLoc loc,
                               std::string* bytes);
  std::string_view ProtectKeyInEffect() const;
  void DecryptDataBlock(const PragmaKeywordExpression& expr, SourceLoc loc,
                        int depth, std::string& output);
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
  // The protected envelopes the protect pragma expressions seen so far have
  // opened and closed. The envelopes describe regions of the source text, so
  // the state outlives any one directive and is read off the preprocessor
  // rather than off the text it produced.
  const ProtectEnvelopeState& ProtectEnvelopes() const {
    return protect_envelopes_;
  }
  // The values the protect pragma keywords of §34.4 have been given by the
  // source text read so far. Their scope is lexical rather than declarative,
  // so it neither begins nor ends with a declaration, and it carries from one
  // file of the compilation input into the next and into every file they
  // include. That is why it is read off the preprocessor, which spans all of
  // them, rather than off any one text it produced.
  const ProtectKeywordScope& ProtectKeywords() const {
    return protect_keywords_;
  }
  // The key that opens the digest of whatever the reading has reached, which
  // §34.5.18 has selected by combining the entity in effect for the digest
  // with the name in effect for its key. Empty where that pair selects none of
  // the keys the user supplied.
  //
  // Like the values it is built from, this belongs to a position in the text
  // rather than to any one directive, which is why it is read off the
  // preprocessor as the reading passes rather than off a text it produced.
  std::string_view DigestKeyInEffect() const;

  // The identifier naming the algorithm the message digests of whatever the
  // reading has reached are computed with, which §34.5.21 has the
  // digest_method pragma expression specify. On the writing side it names the
  // algorithm the digests of the blocks written after it are produced by; on
  // the reading side it names the algorithm a digest is regenerated from a
  // data block with, which is why a text is read for it as well as written
  // with it.
  //
  // A text that has stated no digest_method is read under the default that
  // subclause's own file settles, §34.4 filling a keyword no directive has
  // written from its default and the standard settling none for this one.
  //
  // Like the values it is built from, it belongs to the position the reading
  // has reached rather than to any one directive, which is why it is read off
  // the preprocessor as the reading passes.
  std::string DigestMethodInEffect() const;

  // The identifier naming the cipher the message digests of whatever the
  // reading has reached are encrypted under, which §34.5.17 has the
  // digest_key_method pragma expression specify. On the writing side it names
  // the cipher a region's digests are put under; on the reading side it names
  // the cipher a digest block is opened with, which is why a text is read for
  // it as well as written with it.
  //
  // A text that has stated none is read under the cipher its data are under,
  // which is the default §34.5.17 settles rather than one of this
  // implementation's choosing.
  //
  // Like the values it is built from, it belongs to the position the reading
  // has reached rather than to any one directive, which is why it is read off
  // the preprocessor as the reading passes.
  std::string DigestKeyMethodInEffect() const;

  // The key §34.5.20 has open the digests of whatever the reading has reached:
  // the one a key block carried for them, and the key the region's data are
  // under where no key block carried one, that being the default the subclause
  // settles for a text that specified none.
  //
  // It is held as the key rather than as a name for one, because that is what a
  // digest_decrypt_key expression carries: the encoded value of a key, written
  // on the line beneath the keyword announcing it. Nothing is read against it
  // and nothing selects among anything with it.
  std::string_view DigestDecryptKeyInEffect() const;

  // The key a protected region's digest block is opened with, which §34.5.22
  // has picked out by the designations a region wrote for its digest's key.
  //
  // The designations are consulted in the order that decides them: a key a key
  // block carried was made for this region and travelled inside the envelope,
  // so it is the key rather than something selecting one; the entity and name a
  // region wrote for its digest select one of the keys the user supplied; and a
  // region that wrote neither has its digest under the key its data are under.
  std::string_view DigestBlockKeyInEffect() const;

  // How the last digest block the reading reached compared against the block it
  // immediately follows, which is the comparison §34.5.22 has a consuming tool
  // authenticate a protected region by.
  //
  // A comparison that came out wrong is reported where it happened, that being
  // the one outcome saying something happened to the data. The other two are
  // not reported and are still worth reading: a digest this reader could not
  // open is one written for a reader holding another key, and a reading that
  // reached no digest at all read a text that was never asked to carry one.
  ProtectDigestCheck LastDigestBlockCheck() const {
    return last_digest_block_check_;
  }

  // The identifier naming the algorithm the keys of whatever the reading has
  // reached are encrypted under, which §34.5.24 has the key_method pragma
  // expression specify. On the writing side it names the algorithm a region's
  // keys are put under; on the reading side it names the algorithm the block
  // holding those keys is opened with, which is why a text is read for it as
  // well as written with it.
  //
  // Empty where no directive has named one, this subclause settling no default
  // and §34.4 filling an unwritten keyword from a default that is not there to
  // fill it. A key block standing where nothing has been named is left unopened
  // rather than opened under a guess.
  //
  // Like the value it is built from, it belongs to the position the reading has
  // reached rather than to any one directive, which is why it is read off the
  // preprocessor as the reading passes.
  std::string KeyMethodInEffect() const;

  // The coding scheme, line length and byte count the encoding pragma
  // expression in effect states, which §34.5.9 has every encoded value of a
  // protected envelope written and read under: the block carrying its data,
  // the block carrying its keys, and the encoded value §34.5.26 writes on the
  // line beneath the keyword announcing a public key.
  //
  // A text that has stated no encoding is read in this implementation's own
  // scheme, §34.4 filling a keyword no directive has written from its default
  // and the standard settling no default for this one.
  //
  // Like the values it is built from, it belongs to the position the reading
  // has reached rather than to any one directive, which is why it is read off
  // the preprocessor as the reading passes.
  ProtectEncoding ProtectEncodingInEffect() const;

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
  ProtectEnvelopeState protect_envelopes_;
  ProtectKeywordScope protect_keywords_;
  // The designations the source text has written for the keys of the entities
  // it names. They are unique for the entity they are written under, so they
  // accumulate across the whole compilation input alongside the keyword values
  // themselves rather than starting over at any point within it.
  ProtectKeyDesignations protect_key_designations_;
  // The same, for the entity §34.5.23 names as having provided the keys a
  // region's own keys are under. That entity is a different one from the one
  // whose keys the data are under -- a producer may hold the two apart -- so
  // its designations are unique for it rather than for the other, and they
  // accumulate on their own.
  ProtectKeyDesignations protect_key_block_designations_;
  // Whether the line about to be read is the encoded value of a public key,
  // which is what §34.5.26 makes of the line following the keyword announcing
  // one. The announcement and the value are two lines, so what the first said
  // is carried here until the second arrives.
  bool key_public_key_value_next_ = false;
  // The same, for the two keywords whose definitions speak for the line after
  // them: §34.5.27's, which says a key block begins there, and §34.5.14's,
  // which says the encoded value of the key opening the region's data block is
  // written there.
  bool key_block_value_next_ = false;
  bool data_decrypt_key_value_next_ = false;
  // And for the two whose definitions do the same for the digest a block is
  // checked against: §34.5.20's, which says the key opening that digest is
  // written on the line after it, and §34.5.22's, which says the digest itself
  // is.
  bool digest_decrypt_key_value_next_ = false;
  bool digest_block_value_next_ = false;
  // The key §34.5.14 has open a protected region's data block, recovered from
  // the key block that carried it.
  //
  // It is held as the key rather than among the keyword values because that is
  // what it is: those record what a source text wrote, and this came out of an
  // encrypted block as the key itself, so nothing is read against it and
  // nothing selects among anything with it. Empty until a key block has been
  // opened, which is every reading of a text that carries none.
  std::string data_decrypt_key_;
  // The key §34.5.20 has open a protected region's digest block, recovered from
  // the key block that carried it. It is held apart from the key that opens the
  // data for the reason the subclause gives it a keyword of its own: a reader
  // holding the one has not thereby been given the other, and a digest under
  // the very key its data are under could be recomputed by whoever could alter
  // them.
  std::string digest_decrypt_key_;
  // §34.5.22 has the digest a digest block carries checked against the block it
  // immediately follows, so what the reading last recovered is held here
  // until the digest arrives. Empty where nothing was recovered to check, which
  // is what a reader that could not open the block above sees; a digest with
  // nothing to check is passed over rather than reported, several key blocks of
  // one envelope being alternative ways in and a reader being expected to open
  // only its own.
  ProtectDigestTarget digest_target_;
  // The outcome of the last such comparison, standing at the value that means
  // no digest has been reached until one has been.
  ProtectDigestCheck last_digest_block_check_ = ProtectDigestCheck::kNotChecked;

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
