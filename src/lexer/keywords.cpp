#include "lexer/keywords.h"

#include <unordered_map>

namespace delta {

static const std::unordered_map<std::string_view, TokenKind>& KeywordMap() {
  static const std::unordered_map<std::string_view, TokenKind> kMap = {
      {"module", TokenKind::kKwModule},
      {"endmodule", TokenKind::kKwEndmodule},
      {"input", TokenKind::kKwInput},
      {"output", TokenKind::kKwOutput},
      {"inout", TokenKind::kKwInout},
      {"ref", TokenKind::kKwRef},
      {"wire", TokenKind::kKwWire},
      {"reg", TokenKind::kKwReg},
      {"logic", TokenKind::kKwLogic},
      {"bit", TokenKind::kKwBit},
      {"byte", TokenKind::kKwByte},
      {"shortint", TokenKind::kKwShortint},
      {"int", TokenKind::kKwInt},
      {"longint", TokenKind::kKwLongint},
      {"integer", TokenKind::kKwInteger},
      {"real", TokenKind::kKwReal},
      {"shortreal", TokenKind::kKwShortreal},
      {"realtime", TokenKind::kKwRealtime},
      {"time", TokenKind::kKwTime},
      {"string", TokenKind::kKwString},
      {"chandle", TokenKind::kKwChandle},
      {"void", TokenKind::kKwVoid},
      {"enum", TokenKind::kKwEnum},
      {"struct", TokenKind::kKwStruct},
      {"union", TokenKind::kKwUnion},
      {"typedef", TokenKind::kKwTypedef},
      {"class", TokenKind::kKwClass},
      {"extends", TokenKind::kKwExtends},
      {"interface", TokenKind::kKwInterface},
      {"endinterface", TokenKind::kKwEndinterface},
      {"package", TokenKind::kKwPackage},
      {"endpackage", TokenKind::kKwEndpackage},
      {"program", TokenKind::kKwProgram},
      {"endprogram", TokenKind::kKwEndprogram},
      {"parameter", TokenKind::kKwParameter},
      {"localparam", TokenKind::kKwLocalparam},
      {"specparam", TokenKind::kKwSpecparam},
      {"assign", TokenKind::kKwAssign},
      {"deassign", TokenKind::kKwDeassign},
      {"always", TokenKind::kKwAlways},
      {"always_comb", TokenKind::kKwAlwaysComb},
      {"always_ff", TokenKind::kKwAlwaysFF},
      {"always_latch", TokenKind::kKwAlwaysLatch},
      {"initial", TokenKind::kKwInitial},
      {"final", TokenKind::kKwFinal},
      {"begin", TokenKind::kKwBegin},
      {"end", TokenKind::kKwEnd},
      {"fork", TokenKind::kKwFork},
      {"join", TokenKind::kKwJoin},
      {"join_any", TokenKind::kKwJoinAny},
      {"join_none", TokenKind::kKwJoinNone},
      {"if", TokenKind::kKwIf},
      {"else", TokenKind::kKwElse},
      {"case", TokenKind::kKwCase},
      {"casex", TokenKind::kKwCasex},
      {"casez", TokenKind::kKwCasez},
      {"endcase", TokenKind::kKwEndcase},
      {"for", TokenKind::kKwFor},
      {"forever", TokenKind::kKwForever},
      {"while", TokenKind::kKwWhile},
      {"do", TokenKind::kKwDo},
      {"repeat", TokenKind::kKwRepeat},
      {"break", TokenKind::kKwBreak},
      {"continue", TokenKind::kKwContinue},
      {"return", TokenKind::kKwReturn},
      {"function", TokenKind::kKwFunction},
      {"endfunction", TokenKind::kKwEndfunction},
      {"task", TokenKind::kKwTask},
      {"endtask", TokenKind::kKwEndtask},
      {"generate", TokenKind::kKwGenerate},
      {"endgenerate", TokenKind::kKwEndgenerate},
      {"genvar", TokenKind::kKwGenvar},
      {"posedge", TokenKind::kKwPosedge},
      {"negedge", TokenKind::kKwNegedge},
      {"edge", TokenKind::kKwEdge},
      {"or", TokenKind::kKwOr},
      {"and", TokenKind::kKwAnd},
      {"not", TokenKind::kKwNot},
      {"supply0", TokenKind::kKwSupply0},
      {"supply1", TokenKind::kKwSupply1},
      {"tri", TokenKind::kKwTri},
      {"triand", TokenKind::kKwTriand},
      {"trior", TokenKind::kKwTrior},
      {"tri0", TokenKind::kKwTri0},
      {"tri1", TokenKind::kKwTri1},
      {"trireg", TokenKind::kKwTrireg},
      {"wand", TokenKind::kKwWand},
      {"wor", TokenKind::kKwWor},
      {"uwire", TokenKind::kKwUwire},
      {"signed", TokenKind::kKwSigned},
      {"unsigned", TokenKind::kKwUnsigned},
      {"automatic", TokenKind::kKwAutomatic},
      {"static", TokenKind::kKwStatic},
      {"const", TokenKind::kKwConst},
      {"var", TokenKind::kKwVar},
      {"import", TokenKind::kKwImport},
      {"export", TokenKind::kKwExport},
      {"force", TokenKind::kKwForce},
      {"release", TokenKind::kKwRelease},
      {"wait", TokenKind::kKwWait},
      {"disable", TokenKind::kKwDisable},
      {"null", TokenKind::kKwNull},
      {"this", TokenKind::kKwThis},
      {"super", TokenKind::kKwSuper},
      {"new", TokenKind::kKwNew},
      {"packed", TokenKind::kKwPacked},
      {"tagged", TokenKind::kKwTagged},
      {"default", TokenKind::kKwDefault},
      {"unique", TokenKind::kKwUnique},
      {"unique0", TokenKind::kKwUnique0},
      {"priority", TokenKind::kKwPriority},
  };
  return kMap;
}

std::optional<TokenKind> LookupKeyword(std::string_view text) {
  const auto& map = KeywordMap();
  auto it = map.find(text);
  if (it != map.end()) {
    return it->second;
  }
  return std::nullopt;
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
    default:
      return "token";
  }
}

}  // namespace delta
