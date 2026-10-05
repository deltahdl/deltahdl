#pragma once

#include <vector>

#include "parser/ast_class.h"
#include "parser/ast_expr.h"

namespace delta {

class Parser;

// §18.5 (A.1.10): the parse of a constraint block's items in source order
// into ClassMember::constraint_items, read beside the token scan that fills
// the block's other tables and leaving the scan where it found it. A friend of
// Parser, defined in src/parser/parser_constraint_items.cpp.
struct ParserConstraintItemHelpers {
  // The items from just past the block's '{' through its '}', into `member`.
  static void Capture(Parser& p, ClassMember* member);
  static bool ParseItemsToBrace(Parser& p, std::vector<ConstraintItem*>& out);
  static ConstraintItem* ParseExpressionItem(Parser& p);
  static bool ParseSet(Parser& p, std::vector<ConstraintItem*>& out);
  static bool ParseIfElse(Parser& p, ConstraintItem& item);
  static bool ParseForeach(Parser& p, ConstraintItem& item);
  static bool ParseUnique(Parser& p, ConstraintItem& item);
  static bool ParseSolveBefore(Parser& p, ConstraintItem& item);
  static bool ParseExpressionOrDist(Parser& p, ConstraintItem& item);
  static bool ParseDistList(Parser& p, ConstraintItem& item);
  static bool ParseExprList(Parser& p, std::vector<Expr*>& out);
};

}  // namespace delta
