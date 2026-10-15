// §29.8: the instantiation of a user-defined primitive. Moved out of
// parser_udp.cpp, which reached the size the assert-no-oversized-source-files
// job fails at.

#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_module.h"
#include "parser/parser.h"
#include "parser/parser_instance_internal.h"

namespace delta {

// Whether the item at hand, which opens with a name the parser holds no
// declaration for, is written in a form only a UDP instance takes. §29.3 lets
// a UDP be declared anywhere, so its name may not be known yet. §29.8 gives
// the instance a gate's drive strength, delay2 and optional name. A module
// instance writes `#` only before the parentheses of a parameter value
// assignment, and names its instance before any `(` (A.4.1.1), so a `(` after
// the name, which opens a drive strength or an unnamed instance's terminals,
// and a `#` with no `(` after it, which opens a delay, are a UDP's. `#(` is
// left to the module instance it may be, and
// Elaborator::ReclassifyForwardUdpInstances turns it into a UDP instance where
// the name proves to be one.
bool Parser::AtUdpOnlyInstanceForm() {
  if (Check(TokenKind::kLParen)) return true;
  if (!Check(TokenKind::kHash)) return false;
  auto saved = lexer_.SavePos();
  Consume();
  bool delay = !Check(TokenKind::kLParen);
  lexer_.RestorePos(saved);
  return delay;
}

// A.5.4's udp_instance, `[ name_of_instance ] ( output_terminal ,
// input_terminal { , input_terminal } )`: two terminals at least, the first
// a net_lvalue under A.3.3. The parser had read the terminal list as any list
// of expressions and left both to elaboration, which reports the count for a
// primitive it resolves and the output terminal for none; each is now reported
// where the instance is read, the count under A.5.4 and the terminal under
// §28.3 as a gate's is, since §29.8 has a UDP instance written the way a gate
// instance is.
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
