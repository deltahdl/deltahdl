#pragma once

#include <vector>

#include "parser/ast_class.h"
#include "parser/ast_expr.h"

namespace delta {

class Parser;

struct ParserConstraintItemHelpers {
  static void Capture(Parser& p, ClassMember* member);
  static void ReportLocalQualifiers(Parser& p);
  static bool ParseItemsToBrace(Parser& p, std::vector<ConstraintItem*>& out,
                                bool in_set);
  static ConstraintItem* ParseExpressionItem(Parser& p);
  static ConstraintItem* ParseSetItem(Parser& p);
  static bool ParseSet(Parser& p, std::vector<ConstraintItem*>& out);
  static bool ParseIfElse(Parser& p, ConstraintItem& item);
  static bool ParseForeach(Parser& p, ConstraintItem& item);
  static bool ParseUnique(Parser& p, ConstraintItem& item);
  static bool ParseSolveBefore(Parser& p, ConstraintItem& item);
  static bool ParseExpressionOrDist(Parser& p, ConstraintItem& item);
  static bool ParseDistList(Parser& p, ConstraintItem& item);
  static Expr* ParsePrimary(Parser& p);
  static bool ParsePrimaryList(Parser& p, std::vector<Expr*>& out);
};

}  // namespace delta
