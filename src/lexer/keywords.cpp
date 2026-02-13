#include "lexer/keywords.h"

#include <unordered_map>
#include <unordered_set>

namespace delta {
namespace {

using V = KeywordVersion;

struct KeywordEntry {
  TokenKind kind;
  KeywordVersion min_version;
};

const std::unordered_map<std::string_view, KeywordEntry> kKeywordMap = {
    // IEEE 1364-1995 (Table 22-1)
    {"always", {TokenKind::kKwAlways, V::kVer13641995}},
    {"and", {TokenKind::kKwAnd, V::kVer13641995}},
    {"assign", {TokenKind::kKwAssign, V::kVer13641995}},
    {"begin", {TokenKind::kKwBegin, V::kVer13641995}},
    {"buf", {TokenKind::kKwBuf, V::kVer13641995}},
    {"bufif0", {TokenKind::kKwBufif0, V::kVer13641995}},
    {"bufif1", {TokenKind::kKwBufif1, V::kVer13641995}},
    {"case", {TokenKind::kKwCase, V::kVer13641995}},
    {"casex", {TokenKind::kKwCasex, V::kVer13641995}},
    {"casez", {TokenKind::kKwCasez, V::kVer13641995}},
    {"cmos", {TokenKind::kKwCmos, V::kVer13641995}},
    {"deassign", {TokenKind::kKwDeassign, V::kVer13641995}},
    {"default", {TokenKind::kKwDefault, V::kVer13641995}},
    {"defparam", {TokenKind::kKwDefparam, V::kVer13641995}},
    {"disable", {TokenKind::kKwDisable, V::kVer13641995}},
    {"edge", {TokenKind::kKwEdge, V::kVer13641995}},
    {"else", {TokenKind::kKwElse, V::kVer13641995}},
    {"end", {TokenKind::kKwEnd, V::kVer13641995}},
    {"endcase", {TokenKind::kKwEndcase, V::kVer13641995}},
    {"endfunction", {TokenKind::kKwEndfunction, V::kVer13641995}},
    {"endmodule", {TokenKind::kKwEndmodule, V::kVer13641995}},
    {"endprimitive", {TokenKind::kKwEndprimitive, V::kVer13641995}},
    {"endspecify", {TokenKind::kKwEndspecify, V::kVer13641995}},
    {"endtable", {TokenKind::kKwEndtable, V::kVer13641995}},
    {"endtask", {TokenKind::kKwEndtask, V::kVer13641995}},
    {"event", {TokenKind::kKwEvent, V::kVer13641995}},
    {"for", {TokenKind::kKwFor, V::kVer13641995}},
    {"force", {TokenKind::kKwForce, V::kVer13641995}},
    {"forever", {TokenKind::kKwForever, V::kVer13641995}},
    {"fork", {TokenKind::kKwFork, V::kVer13641995}},
    {"function", {TokenKind::kKwFunction, V::kVer13641995}},
    {"highz0", {TokenKind::kKwHighz0, V::kVer13641995}},
    {"highz1", {TokenKind::kKwHighz1, V::kVer13641995}},
    {"if", {TokenKind::kKwIf, V::kVer13641995}},
    {"ifnone", {TokenKind::kKwIfnone, V::kVer13641995}},
    {"initial", {TokenKind::kKwInitial, V::kVer13641995}},
    {"inout", {TokenKind::kKwInout, V::kVer13641995}},
    {"input", {TokenKind::kKwInput, V::kVer13641995}},
    {"integer", {TokenKind::kKwInteger, V::kVer13641995}},
    {"join", {TokenKind::kKwJoin, V::kVer13641995}},
    {"large", {TokenKind::kKwLarge, V::kVer13641995}},
    {"macromodule", {TokenKind::kKwMacromodule, V::kVer13641995}},
    {"medium", {TokenKind::kKwMedium, V::kVer13641995}},
    {"module", {TokenKind::kKwModule, V::kVer13641995}},
    {"nand", {TokenKind::kKwNand, V::kVer13641995}},
    {"negedge", {TokenKind::kKwNegedge, V::kVer13641995}},
    {"nmos", {TokenKind::kKwNmos, V::kVer13641995}},
    {"nor", {TokenKind::kKwNor, V::kVer13641995}},
    {"not", {TokenKind::kKwNot, V::kVer13641995}},
    {"notif0", {TokenKind::kKwNotif0, V::kVer13641995}},
    {"notif1", {TokenKind::kKwNotif1, V::kVer13641995}},
    {"or", {TokenKind::kKwOr, V::kVer13641995}},
    {"output", {TokenKind::kKwOutput, V::kVer13641995}},
    {"parameter", {TokenKind::kKwParameter, V::kVer13641995}},
    {"pmos", {TokenKind::kKwPmos, V::kVer13641995}},
    {"posedge", {TokenKind::kKwPosedge, V::kVer13641995}},
    {"primitive", {TokenKind::kKwPrimitive, V::kVer13641995}},
    {"pull0", {TokenKind::kKwPull0, V::kVer13641995}},
    {"pull1", {TokenKind::kKwPull1, V::kVer13641995}},
    {"pulldown", {TokenKind::kKwPulldown, V::kVer13641995}},
    {"pullup", {TokenKind::kKwPullup, V::kVer13641995}},
    {"rcmos", {TokenKind::kKwRcmos, V::kVer13641995}},
    {"real", {TokenKind::kKwReal, V::kVer13641995}},
    {"realtime", {TokenKind::kKwRealtime, V::kVer13641995}},
    {"reg", {TokenKind::kKwReg, V::kVer13641995}},
    {"release", {TokenKind::kKwRelease, V::kVer13641995}},
    {"repeat", {TokenKind::kKwRepeat, V::kVer13641995}},
    {"rnmos", {TokenKind::kKwRnmos, V::kVer13641995}},
    {"rpmos", {TokenKind::kKwRpmos, V::kVer13641995}},
    {"rtran", {TokenKind::kKwRtran, V::kVer13641995}},
    {"rtranif0", {TokenKind::kKwRtranif0, V::kVer13641995}},
    {"rtranif1", {TokenKind::kKwRtranif1, V::kVer13641995}},
    {"scalared", {TokenKind::kKwScalared, V::kVer13641995}},
    {"small", {TokenKind::kKwSmall, V::kVer13641995}},
    {"specify", {TokenKind::kKwSpecify, V::kVer13641995}},
    {"specparam", {TokenKind::kKwSpecparam, V::kVer13641995}},
    {"strong0", {TokenKind::kKwStrong0, V::kVer13641995}},
    {"strong1", {TokenKind::kKwStrong1, V::kVer13641995}},
    {"supply0", {TokenKind::kKwSupply0, V::kVer13641995}},
    {"supply1", {TokenKind::kKwSupply1, V::kVer13641995}},
    {"table", {TokenKind::kKwTable, V::kVer13641995}},
    {"task", {TokenKind::kKwTask, V::kVer13641995}},
    {"time", {TokenKind::kKwTime, V::kVer13641995}},
    {"tran", {TokenKind::kKwTran, V::kVer13641995}},
    {"tranif0", {TokenKind::kKwTranif0, V::kVer13641995}},
    {"tranif1", {TokenKind::kKwTranif1, V::kVer13641995}},
    {"tri", {TokenKind::kKwTri, V::kVer13641995}},
    {"tri0", {TokenKind::kKwTri0, V::kVer13641995}},
    {"tri1", {TokenKind::kKwTri1, V::kVer13641995}},
    {"triand", {TokenKind::kKwTriand, V::kVer13641995}},
    {"trior", {TokenKind::kKwTrior, V::kVer13641995}},
    {"trireg", {TokenKind::kKwTrireg, V::kVer13641995}},
    {"vectored", {TokenKind::kKwVectored, V::kVer13641995}},
    {"wait", {TokenKind::kKwWait, V::kVer13641995}},
    {"wand", {TokenKind::kKwWand, V::kVer13641995}},
    {"weak0", {TokenKind::kKwWeak0, V::kVer13641995}},
    {"weak1", {TokenKind::kKwWeak1, V::kVer13641995}},
    {"while", {TokenKind::kKwWhile, V::kVer13641995}},
    {"wire", {TokenKind::kKwWire, V::kVer13641995}},
    {"wor", {TokenKind::kKwWor, V::kVer13641995}},
    {"xnor", {TokenKind::kKwXnor, V::kVer13641995}},
    {"xor", {TokenKind::kKwXor, V::kVer13641995}},
    // IEEE 1364-2001 (Table 22-2)
    {"automatic", {TokenKind::kKwAutomatic, V::kVer13642001}},
    {"cell", {TokenKind::kKwCell, V::kVer13642001}},
    {"config", {TokenKind::kKwConfig, V::kVer13642001}},
    {"design", {TokenKind::kKwDesign, V::kVer13642001}},
    {"endconfig", {TokenKind::kKwEndconfig, V::kVer13642001}},
    {"endgenerate", {TokenKind::kKwEndgenerate, V::kVer13642001}},
    {"generate", {TokenKind::kKwGenerate, V::kVer13642001}},
    {"genvar", {TokenKind::kKwGenvar, V::kVer13642001}},
    {"incdir", {TokenKind::kKwIncdir, V::kVer13642001}},
    {"include", {TokenKind::kKwInclude, V::kVer13642001}},
    {"instance", {TokenKind::kKwInstance, V::kVer13642001}},
    {"liblist", {TokenKind::kKwLiblist, V::kVer13642001}},
    {"library", {TokenKind::kKwLibrary, V::kVer13642001}},
    {"localparam", {TokenKind::kKwLocalparam, V::kVer13642001}},
    {"noshowcancelled", {TokenKind::kKwNoshowcancelled, V::kVer13642001}},
    {"pulsestyle_ondetect",
     {TokenKind::kKwPulsestyleOndetect, V::kVer13642001}},
    {"pulsestyle_onevent", {TokenKind::kKwPulsestyleOnevent, V::kVer13642001}},
    {"showcancelled", {TokenKind::kKwShowcancelled, V::kVer13642001}},
    {"signed", {TokenKind::kKwSigned, V::kVer13642001}},
    {"unsigned", {TokenKind::kKwUnsigned, V::kVer13642001}},
    {"use", {TokenKind::kKwUse, V::kVer13642001}},
    // IEEE 1364-2005 (Table 22-3)
    {"uwire", {TokenKind::kKwUwire, V::kVer13642005}},
    // IEEE 1800-2005 (Table 22-4)
    {"alias", {TokenKind::kKwAlias, V::kVer18002005}},
    {"always_comb", {TokenKind::kKwAlwaysComb, V::kVer18002005}},
    {"always_ff", {TokenKind::kKwAlwaysFF, V::kVer18002005}},
    {"always_latch", {TokenKind::kKwAlwaysLatch, V::kVer18002005}},
    {"assert", {TokenKind::kKwAssert, V::kVer18002005}},
    {"assume", {TokenKind::kKwAssume, V::kVer18002005}},
    {"before", {TokenKind::kKwBefore, V::kVer18002005}},
    {"bind", {TokenKind::kKwBind, V::kVer18002005}},
    {"bins", {TokenKind::kKwBins, V::kVer18002005}},
    {"binsof", {TokenKind::kKwBinsof, V::kVer18002005}},
    {"bit", {TokenKind::kKwBit, V::kVer18002005}},
    {"break", {TokenKind::kKwBreak, V::kVer18002005}},
    {"byte", {TokenKind::kKwByte, V::kVer18002005}},
    {"chandle", {TokenKind::kKwChandle, V::kVer18002005}},
    {"class", {TokenKind::kKwClass, V::kVer18002005}},
    {"clocking", {TokenKind::kKwClocking, V::kVer18002005}},
    {"const", {TokenKind::kKwConst, V::kVer18002005}},
    {"constraint", {TokenKind::kKwConstraint, V::kVer18002005}},
    {"context", {TokenKind::kKwContext, V::kVer18002005}},
    {"continue", {TokenKind::kKwContinue, V::kVer18002005}},
    {"cover", {TokenKind::kKwCover, V::kVer18002005}},
    {"covergroup", {TokenKind::kKwCovergroup, V::kVer18002005}},
    {"coverpoint", {TokenKind::kKwCoverpoint, V::kVer18002005}},
    {"cross", {TokenKind::kKwCross, V::kVer18002005}},
    {"dist", {TokenKind::kKwDist, V::kVer18002005}},
    {"do", {TokenKind::kKwDo, V::kVer18002005}},
    {"endclass", {TokenKind::kKwEndclass, V::kVer18002005}},
    {"endclocking", {TokenKind::kKwEndclocking, V::kVer18002005}},
    {"endgroup", {TokenKind::kKwEndgroup, V::kVer18002005}},
    {"endinterface", {TokenKind::kKwEndinterface, V::kVer18002005}},
    {"endpackage", {TokenKind::kKwEndpackage, V::kVer18002005}},
    {"endprogram", {TokenKind::kKwEndprogram, V::kVer18002005}},
    {"endproperty", {TokenKind::kKwEndproperty, V::kVer18002005}},
    {"endsequence", {TokenKind::kKwEndsequence, V::kVer18002005}},
    {"enum", {TokenKind::kKwEnum, V::kVer18002005}},
    {"expect", {TokenKind::kKwExpect, V::kVer18002005}},
    {"export", {TokenKind::kKwExport, V::kVer18002005}},
    {"extends", {TokenKind::kKwExtends, V::kVer18002005}},
    {"extern", {TokenKind::kKwExtern, V::kVer18002005}},
    {"final", {TokenKind::kKwFinal, V::kVer18002005}},
    {"first_match", {TokenKind::kKwFirstMatch, V::kVer18002005}},
    {"foreach", {TokenKind::kKwForeach, V::kVer18002005}},
    {"forkjoin", {TokenKind::kKwForkjoin, V::kVer18002005}},
    {"iff", {TokenKind::kKwIff, V::kVer18002005}},
    {"ignore_bins", {TokenKind::kKwIgnoreBins, V::kVer18002005}},
    {"illegal_bins", {TokenKind::kKwIllegalBins, V::kVer18002005}},
    {"import", {TokenKind::kKwImport, V::kVer18002005}},
    {"inside", {TokenKind::kKwInside, V::kVer18002005}},
    {"int", {TokenKind::kKwInt, V::kVer18002005}},
    {"interface", {TokenKind::kKwInterface, V::kVer18002005}},
    {"intersect", {TokenKind::kKwIntersect, V::kVer18002005}},
    {"join_any", {TokenKind::kKwJoinAny, V::kVer18002005}},
    {"join_none", {TokenKind::kKwJoinNone, V::kVer18002005}},
    {"local", {TokenKind::kKwLocal, V::kVer18002005}},
    {"logic", {TokenKind::kKwLogic, V::kVer18002005}},
    {"longint", {TokenKind::kKwLongint, V::kVer18002005}},
    {"matches", {TokenKind::kKwMatches, V::kVer18002005}},
    {"modport", {TokenKind::kKwModport, V::kVer18002005}},
    {"new", {TokenKind::kKwNew, V::kVer18002005}},
    {"null", {TokenKind::kKwNull, V::kVer18002005}},
    {"package", {TokenKind::kKwPackage, V::kVer18002005}},
    {"packed", {TokenKind::kKwPacked, V::kVer18002005}},
    {"priority", {TokenKind::kKwPriority, V::kVer18002005}},
    {"program", {TokenKind::kKwProgram, V::kVer18002005}},
    {"property", {TokenKind::kKwProperty, V::kVer18002005}},
    {"protected", {TokenKind::kKwProtected, V::kVer18002005}},
    {"pure", {TokenKind::kKwPure, V::kVer18002005}},
    {"rand", {TokenKind::kKwRand, V::kVer18002005}},
    {"randc", {TokenKind::kKwRandc, V::kVer18002005}},
    {"randcase", {TokenKind::kKwRandcase, V::kVer18002005}},
    {"randsequence", {TokenKind::kKwRandsequence, V::kVer18002005}},
    {"ref", {TokenKind::kKwRef, V::kVer18002005}},
    {"return", {TokenKind::kKwReturn, V::kVer18002005}},
    {"sequence", {TokenKind::kKwSequence, V::kVer18002005}},
    {"shortint", {TokenKind::kKwShortint, V::kVer18002005}},
    {"shortreal", {TokenKind::kKwShortreal, V::kVer18002005}},
    {"solve", {TokenKind::kKwSolve, V::kVer18002005}},
    {"static", {TokenKind::kKwStatic, V::kVer18002005}},
    {"string", {TokenKind::kKwString, V::kVer18002005}},
    {"struct", {TokenKind::kKwStruct, V::kVer18002005}},
    {"super", {TokenKind::kKwSuper, V::kVer18002005}},
    {"tagged", {TokenKind::kKwTagged, V::kVer18002005}},
    {"this", {TokenKind::kKwThis, V::kVer18002005}},
    {"throughout", {TokenKind::kKwThroughout, V::kVer18002005}},
    {"timeprecision", {TokenKind::kKwTimeprecision, V::kVer18002005}},
    {"timeunit", {TokenKind::kKwTimeunit, V::kVer18002005}},
    {"type", {TokenKind::kKwType, V::kVer18002005}},
    {"typedef", {TokenKind::kKwTypedef, V::kVer18002005}},
    {"union", {TokenKind::kKwUnion, V::kVer18002005}},
    {"unique", {TokenKind::kKwUnique, V::kVer18002005}},
    {"var", {TokenKind::kKwVar, V::kVer18002005}},
    {"virtual", {TokenKind::kKwVirtual, V::kVer18002005}},
    {"void", {TokenKind::kKwVoid, V::kVer18002005}},
    {"wait_order", {TokenKind::kKwWaitOrder, V::kVer18002005}},
    {"wildcard", {TokenKind::kKwWildcard, V::kVer18002005}},
    {"with", {TokenKind::kKwWith, V::kVer18002005}},
    {"within", {TokenKind::kKwWithin, V::kVer18002005}},
    // IEEE 1800-2009 (Table 22-5)
    {"accept_on", {TokenKind::kKwAcceptOn, V::kVer18002009}},
    {"checker", {TokenKind::kKwChecker, V::kVer18002009}},
    {"endchecker", {TokenKind::kKwEndchecker, V::kVer18002009}},
    {"eventually", {TokenKind::kKwEventually, V::kVer18002009}},
    {"global", {TokenKind::kKwGlobal, V::kVer18002009}},
    {"implies", {TokenKind::kKwImplies, V::kVer18002009}},
    {"let", {TokenKind::kKwLet, V::kVer18002009}},
    {"nexttime", {TokenKind::kKwNexttime, V::kVer18002009}},
    {"reject_on", {TokenKind::kKwRejectOn, V::kVer18002009}},
    {"restrict", {TokenKind::kKwRestrict, V::kVer18002009}},
    {"s_always", {TokenKind::kKwSAlways, V::kVer18002009}},
    {"s_eventually", {TokenKind::kKwSEventually, V::kVer18002009}},
    {"s_nexttime", {TokenKind::kKwSNexttime, V::kVer18002009}},
    {"s_until", {TokenKind::kKwSUntil, V::kVer18002009}},
    {"s_until_with", {TokenKind::kKwSUntilWith, V::kVer18002009}},
    {"strong", {TokenKind::kKwStrong, V::kVer18002009}},
    {"sync_accept_on", {TokenKind::kKwSyncAcceptOn, V::kVer18002009}},
    {"sync_reject_on", {TokenKind::kKwSyncRejectOn, V::kVer18002009}},
    {"unique0", {TokenKind::kKwUnique0, V::kVer18002009}},
    {"until", {TokenKind::kKwUntil, V::kVer18002009}},
    {"until_with", {TokenKind::kKwUntilWith, V::kVer18002009}},
    {"untyped", {TokenKind::kKwUntyped, V::kVer18002009}},
    {"weak", {TokenKind::kKwWeak, V::kVer18002009}},
    // IEEE 1800-2012 (Table 22-6)
    {"implements", {TokenKind::kKwImplements, V::kVer18002012}},
    {"interconnect", {TokenKind::kKwInterconnect, V::kVer18002012}},
    {"nettype", {TokenKind::kKwNettype, V::kVer18002012}},
    {"soft", {TokenKind::kKwSoft, V::kVer18002012}},
    // IEEE 1800-2017 and 1800-2023 add no new keywords.
};

// Keywords excluded from the "1364-2001-noconfig" version (§22.14.4).
const std::unordered_set<std::string_view> kNoconfigExcluded = {
    "cell",    "config",   "design",  "endconfig", "incdir",
    "include", "instance", "liblist", "library",   "use",
};

const std::unordered_map<std::string_view, KeywordVersion> kVersionMap = {
    {"1364-1995", V::kVer13641995},
    {"1364-2001", V::kVer13642001},
    {"1364-2001-noconfig", V::kVer13642001Noconfig},
    {"1364-2005", V::kVer13642005},
    {"1800-2005", V::kVer18002005},
    {"1800-2009", V::kVer18002009},
    {"1800-2012", V::kVer18002012},
    {"1800-2017", V::kVer18002017},
    {"1800-2023", V::kVer18002023},
};

}  // namespace

std::optional<KeywordVersion> ParseKeywordVersion(std::string_view spec) {
  auto it = kVersionMap.find(spec);
  if (it != kVersionMap.end()) {
    return it->second;
  }
  return std::nullopt;
}

std::optional<TokenKind> LookupKeyword(std::string_view text,
                                       KeywordVersion version) {
  auto it = kKeywordMap.find(text);
  if (it == kKeywordMap.end()) {
    return std::nullopt;
  }
  auto [kind, min_ver] = it->second;
  if (min_ver > version) {
    return std::nullopt;
  }
  // "1364-2001-noconfig" excludes 10 config-related keywords (§22.14.4).
  if (version == V::kVer13642001Noconfig && min_ver == V::kVer13642001 &&
      kNoconfigExcluded.contains(text)) {
    return std::nullopt;
  }
  return kind;
}

std::string_view TokenKindName(TokenKind kind) {
  switch (kind) {
    case TokenKind::kEof:
      return "EOF";
    case TokenKind::kError:
      return "error";
    case TokenKind::kIntLiteral:
      return "integer literal";
    case TokenKind::kRealLiteral:
      return "real literal";
    case TokenKind::kTimeLiteral:
      return "time literal";
    case TokenKind::kStringLiteral:
      return "string literal";
    case TokenKind::kUnbasedUnsizedLiteral:
      return "unbased unsized literal";
    case TokenKind::kIdentifier:
      return "identifier";
    case TokenKind::kEscapedIdentifier:
      return "escaped identifier";
    case TokenKind::kSystemIdentifier:
      return "system identifier";
    case TokenKind::kSemicolon:
      return "';'";
    case TokenKind::kLParen:
      return "'('";
    case TokenKind::kRParen:
      return "')'";
    case TokenKind::kLBracket:
      return "'['";
    case TokenKind::kRBracket:
      return "']'";
    case TokenKind::kLBrace:
      return "'{'";
    case TokenKind::kRBrace:
      return "'}'";
    case TokenKind::kComma:
      return "','";
    case TokenKind::kDot:
      return "'.'";
    case TokenKind::kColon:
      return "':'";
    case TokenKind::kHash:
      return "'#'";
    case TokenKind::kEq:
      return "'='";
    case TokenKind::kLtEq:
      return "'<='";
    case TokenKind::kApostrophe:
      return "'";
    case TokenKind::kApostropheLBrace:
      return "'{";
    case TokenKind::kAttrStart:
      return "'(*'";
    case TokenKind::kAttrEnd:
      return "'*)'";
    case TokenKind::kPlusSlashMinus:
      return "'+/-'";
    case TokenKind::kPlusPercentMinus:
      return "'+%-'";
    default:
      return "token";
  }
}

}  // namespace delta
