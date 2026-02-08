#include "lexer/keywords.h"

#include <unordered_map>

namespace delta {

static const std::unordered_map<std::string_view, TokenKind>& keyword_map() {
  static const std::unordered_map<std::string_view, TokenKind> map = {
      {"module", TokenKind::KwModule},
      {"endmodule", TokenKind::KwEndmodule},
      {"input", TokenKind::KwInput},
      {"output", TokenKind::KwOutput},
      {"inout", TokenKind::KwInout},
      {"ref", TokenKind::KwRef},
      {"wire", TokenKind::KwWire},
      {"reg", TokenKind::KwReg},
      {"logic", TokenKind::KwLogic},
      {"bit", TokenKind::KwBit},
      {"byte", TokenKind::KwByte},
      {"shortint", TokenKind::KwShortint},
      {"int", TokenKind::KwInt},
      {"longint", TokenKind::KwLongint},
      {"integer", TokenKind::KwInteger},
      {"real", TokenKind::KwReal},
      {"shortreal", TokenKind::KwShortreal},
      {"realtime", TokenKind::KwRealtime},
      {"time", TokenKind::KwTime},
      {"string", TokenKind::KwString},
      {"chandle", TokenKind::KwChandle},
      {"void", TokenKind::KwVoid},
      {"enum", TokenKind::KwEnum},
      {"struct", TokenKind::KwStruct},
      {"union", TokenKind::KwUnion},
      {"typedef", TokenKind::KwTypedef},
      {"class", TokenKind::KwClass},
      {"extends", TokenKind::KwExtends},
      {"interface", TokenKind::KwInterface},
      {"endinterface", TokenKind::KwEndinterface},
      {"package", TokenKind::KwPackage},
      {"endpackage", TokenKind::KwEndpackage},
      {"program", TokenKind::KwProgram},
      {"endprogram", TokenKind::KwEndprogram},
      {"parameter", TokenKind::KwParameter},
      {"localparam", TokenKind::KwLocalparam},
      {"specparam", TokenKind::KwSpecparam},
      {"assign", TokenKind::KwAssign},
      {"deassign", TokenKind::KwDeassign},
      {"always", TokenKind::KwAlways},
      {"always_comb", TokenKind::KwAlwaysComb},
      {"always_ff", TokenKind::KwAlwaysFF},
      {"always_latch", TokenKind::KwAlwaysLatch},
      {"initial", TokenKind::KwInitial},
      {"final", TokenKind::KwFinal},
      {"begin", TokenKind::KwBegin},
      {"end", TokenKind::KwEnd},
      {"fork", TokenKind::KwFork},
      {"join", TokenKind::KwJoin},
      {"join_any", TokenKind::KwJoinAny},
      {"join_none", TokenKind::KwJoinNone},
      {"if", TokenKind::KwIf},
      {"else", TokenKind::KwElse},
      {"case", TokenKind::KwCase},
      {"casex", TokenKind::KwCasex},
      {"casez", TokenKind::KwCasez},
      {"endcase", TokenKind::KwEndcase},
      {"for", TokenKind::KwFor},
      {"forever", TokenKind::KwForever},
      {"while", TokenKind::KwWhile},
      {"do", TokenKind::KwDo},
      {"repeat", TokenKind::KwRepeat},
      {"break", TokenKind::KwBreak},
      {"continue", TokenKind::KwContinue},
      {"return", TokenKind::KwReturn},
      {"function", TokenKind::KwFunction},
      {"endfunction", TokenKind::KwEndfunction},
      {"task", TokenKind::KwTask},
      {"endtask", TokenKind::KwEndtask},
      {"generate", TokenKind::KwGenerate},
      {"endgenerate", TokenKind::KwEndgenerate},
      {"genvar", TokenKind::KwGenvar},
      {"posedge", TokenKind::KwPosedge},
      {"negedge", TokenKind::KwNegedge},
      {"edge", TokenKind::KwEdge},
      {"or", TokenKind::KwOr},
      {"and", TokenKind::KwAnd},
      {"not", TokenKind::KwNot},
      {"supply0", TokenKind::KwSupply0},
      {"supply1", TokenKind::KwSupply1},
      {"tri", TokenKind::KwTri},
      {"triand", TokenKind::KwTriand},
      {"trior", TokenKind::KwTrior},
      {"tri0", TokenKind::KwTri0},
      {"tri1", TokenKind::KwTri1},
      {"trireg", TokenKind::KwTrireg},
      {"wand", TokenKind::KwWand},
      {"wor", TokenKind::KwWor},
      {"uwire", TokenKind::KwUwire},
      {"signed", TokenKind::KwSigned},
      {"unsigned", TokenKind::KwUnsigned},
      {"automatic", TokenKind::KwAutomatic},
      {"static", TokenKind::KwStatic},
      {"const", TokenKind::KwConst},
      {"var", TokenKind::KwVar},
      {"import", TokenKind::KwImport},
      {"export", TokenKind::KwExport},
      {"force", TokenKind::KwForce},
      {"release", TokenKind::KwRelease},
      {"wait", TokenKind::KwWait},
      {"disable", TokenKind::KwDisable},
      {"null", TokenKind::KwNull},
      {"this", TokenKind::KwThis},
      {"super", TokenKind::KwSuper},
      {"new", TokenKind::KwNew},
      {"packed", TokenKind::KwPacked},
      {"tagged", TokenKind::KwTagged},
      {"default", TokenKind::KwDefault},
      {"unique", TokenKind::KwUnique},
      {"unique0", TokenKind::KwUnique0},
      {"priority", TokenKind::KwPriority},
  };
  return map;
}

std::optional<TokenKind> lookup_keyword(std::string_view text) {
  const auto& map = keyword_map();
  auto it = map.find(text);
  if (it != map.end()) {
    return it->second;
  }
  return std::nullopt;
}

std::string_view token_kind_name(TokenKind kind) {
  switch (kind) {
    case TokenKind::Eof:
      return "EOF";
    case TokenKind::Error:
      return "error";
    case TokenKind::IntLiteral:
      return "integer literal";
    case TokenKind::RealLiteral:
      return "real literal";
    case TokenKind::TimeLiteral:
      return "time literal";
    case TokenKind::StringLiteral:
      return "string literal";
    case TokenKind::UnbasedUnsizedLiteral:
      return "unbased unsized literal";
    case TokenKind::Identifier:
      return "identifier";
    case TokenKind::EscapedIdentifier:
      return "escaped identifier";
    case TokenKind::SystemIdentifier:
      return "system identifier";
    case TokenKind::Semicolon:
      return "';'";
    case TokenKind::LParen:
      return "'('";
    case TokenKind::RParen:
      return "')'";
    case TokenKind::LBracket:
      return "'['";
    case TokenKind::RBracket:
      return "']'";
    case TokenKind::LBrace:
      return "'{'";
    case TokenKind::RBrace:
      return "'}'";
    case TokenKind::Comma:
      return "','";
    case TokenKind::Dot:
      return "'.'";
    case TokenKind::Colon:
      return "':'";
    case TokenKind::Hash:
      return "'#'";
    case TokenKind::Eq:
      return "'='";
    case TokenKind::LtEq:
      return "'<='";
    default:
      return "token";
  }
}

}  // namespace delta
