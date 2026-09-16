#pragma once

#include <vector>

#include "common/arena.h"
#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast.h"

namespace delta {

class Parser;

// What a property_spec of the form the evaluation reads holds after its
// clock: the disable condition, and the boolean, the sequence with its
// strength, or the tree of operands that is its body, with the negation
// written before the body.
struct SimpleSpecBody {
  Expr* disable_iff = nullptr;
  Expr* prop = nullptr;
  ModuleItem* sequence = nullptr;
  bool strong = false;
  bool negated = false;
  PropertyExprNode* property = nullptr;
};

// §16.12 to §16.12.6: the parse of the property_spec of a concurrent
// assertion in the forms the evaluation reads, after its clock: the disable
// condition, and a boolean, a sequential property or a property of operands
// under not, or, and, if-else, case, implication, followed-by, implies,
// iff, nexttime, always, until, eventually and the aborts. A
// friend of Parser, defined in src/parser/parser_property_spec.cpp.
struct ParserPropertySpecHelpers {
  static Expr* PropertySpecPlaceholder(Arena& arena, SourceLoc loc);
  static ModuleItem* TryParseSequenceSpec(Parser& p, bool& strong, bool term);
  static bool AheadHolds(Parser& p, TokenKind wanted, bool to_junction);
  static bool BodyHasPropertyJunction(Parser& p);
  static bool AheadOpensKeywordTerm(Parser& p);
  static bool AheadHoldsRepetition(Parser& p);
  static bool AheadHoldsSequenceOperator(Parser& p);
  static PropertyExprNode* NewPropertyNode(Parser& p,
                                           PropertyExprNode::Kind kind);
  static PropertyExprNode* TryParsePropertyGroup(Parser& p, bool& group);
  static Expr* ParsePropertyActualArg(Parser& p, bool& plain);
  static bool ParseNamedActualPrefix(Parser& p, Expr* call, bool& named);
  static bool ParsePropertyActualList(Parser& p, Expr* call, bool& plain);
  static Expr* TryParsePropertyInstance(Parser& p);
  static PropertyExprNode* ParsePropertyIfElse(Parser& p);
  static bool ParsePropertyCaseItem(Parser& p, PropertyExprNode& node);
  static PropertyExprNode* ParsePropertyCase(Parser& p);
  static PropertyExprNode* ParsePropertyNexttime(Parser& p, bool strong);
  static PropertyExprNode* ParsePropertyAbort(Parser& p);
  static PropertyExprNode* ParsePropertyAlways(Parser& p,
                                               PropertyExprNode::Kind kind,
                                               bool strong);
  static PropertyExprNode* TryParseKeywordTerm(Parser& p, bool& read);
  static PropertyExprNode* ParseClockedTerm(Parser& p);
  static PropertyExprNode* ParsePropertyTerm(Parser& p);
  static PropertyExprNode* ParsePropertyAnd(Parser& p);
  static PropertyExprNode* ParsePropertyOr(Parser& p);
  static PropertyExprNode* ParsePropertyImplication(Parser& p);
  static PropertyExprNode* ParsePropertyImplies(Parser& p);
  static PropertyExprNode* ParsePropertyIff(Parser& p);
  static bool ParseSimpleSpecBody(Parser& p, SimpleSpecBody& body);
  static Stmt* MakeSimplePropertyStmt(Parser& p, ModuleItem* item,
                                      StmtKind body_kind,
                                      const SimpleSpecBody& body);
  static PropertyExprNode* TreeOfSpecBody(Parser& p,
                                          const SimpleSpecBody& body);
  static void CapturePropertyTreeBody(Parser& p, ModuleItem* item);
  // §16.10 and §16.13.7: the assertion_variable_declarations at the head
  // of a named property's body, `logic v = e;`, read as a sequence body's
  // are; false where one is malformed. Defined in
  // src/parser/parser_sequence_linear.cpp beside the sequence body's.
  static bool ParsePropertyLocalDecls(Parser& p,
                                      std::vector<SeqLocalDecl>& locals);
};

}  // namespace delta
