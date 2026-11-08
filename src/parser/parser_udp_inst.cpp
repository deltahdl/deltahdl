#include <cstdint>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/parser.h"
#include "parser/parser_instance_internal.h"

namespace delta {

bool Parser::AtUdpOnlyInstanceForm() {
  if (Check(TokenKind::kLParen)) return true;
  if (!Check(TokenKind::kHash)) return false;
  auto saved = lexer_.SavePos();
  Consume();
  bool udp_only = !Check(TokenKind::kLParen);
  if (!udp_only) {
    SkipBalancedParens();
    udp_only = Check(TokenKind::kLParen);
  }
  lexer_.RestorePos(saved);
  return udp_only;
}

ModuleItem* Parser::ParseOneUdpInstance(const Token& udp_tok, SourceLoc loc) {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kUdpInst;
  item->loc = loc;
  item->inst_module = udp_tok.text;
  item->udp_undeclared_at_parse = known_udps_.count(udp_tok.text) == 0;

  ParseGateInstanceTail(*this, item,
                        CheckIdentifier() && !Check(TokenKind::kLParen));
  if (item->gate_terminals.size() < 2) {
    diag_.Error(loc,
                "a UDP instance connects an output terminal and at least one "
                "input terminal",
                Subclause("A.5.4"));
  }
  if (!item->gate_terminals.empty() && !IsNetLvalue(item->gate_terminals[0])) {
    diag_.Error(loc, "output terminal must be a net lvalue", Subclause("28.3"));
  }
  return item;
}

void Parser::ParseUdpInstList(const Token& udp_tok,
                              std::vector<ModuleItem*>& items) {
  auto loc = udp_tok.loc;

  uint8_t str0 = 0;
  uint8_t str1 = 0;
  TryParseStrengthSpec(str0, str1);

  Expr* delay = nullptr;
  Expr* delay_fall = nullptr;
  Expr* decay = nullptr;
  ParseGateDelay(delay, delay_fall, decay);

  if (decay != nullptr) {
    diag_.Error(loc, "UDP instantiation shall have at most two delays",
                Subclause("29.8"));
  }

  auto apply_common = [&](ModuleItem* item) {
    item->drive_strength0 = str0;
    item->drive_strength1 = str1;
    item->gate_delay = delay;
    item->gate_delay_fall = delay_fall;
  };

  auto* first = ParseOneUdpInstance(udp_tok, loc);
  apply_common(first);
  items.push_back(first);
  while (Match(TokenKind::kComma)) {
    auto* next = ParseOneUdpInstance(udp_tok, loc);
    apply_common(next);
    items.push_back(next);
  }
  Expect(TokenKind::kSemicolon, Subclause("29.8"));
}

}  // namespace delta
