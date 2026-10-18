#pragma once

namespace delta {

class Parser;

// §A.2.10: whether the property_spec of a concurrent assertion statement is
// one the grammar admits. The evaluation's own parse,
// Parser::TryParseSimpleConcurrentProperty, reads the specs it evaluates and
// gives up silently on the rest, which are either well-formed specs beyond
// those forms or text that is no property_spec at all; this tells the two
// apart, so the second is reported as the error it is. A friend of Parser,
// defined in src/parser/parser_property_grammar.cpp.
struct ParserPropertyGrammar {
  // The spec from the current token to the parenthesis closing it,
  // `[clocking_event] [disable iff ( expression_or_dist )]` and a
  // property_expr, or a sequence_expr where `sequence` is set, as a cover
  // sequence statement writes it. Answers whether the grammar admits it,
  // reporting it where it does not at the furthest point no reading of the
  // spec gets past; the lexer is left where it was.
  static bool CheckPropertySpec(Parser& p, bool sequence);

 private:
  class Scan;
};

}  // namespace delta
