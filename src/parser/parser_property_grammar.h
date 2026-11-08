#pragma once

#include "lexer/token.h"

namespace delta {

class Parser;

struct ParserPropertyGrammar {
  static bool CheckPropertySpec(Parser& p, bool sequence);

  static bool CheckDeclarationBody(Parser& p, bool sequence, TokenKind end);

 private:
  class Scan;

  static bool Recognize(Parser& p, bool sequence, bool body, TokenKind end);
};

}  // namespace delta
