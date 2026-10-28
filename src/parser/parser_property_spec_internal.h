#pragma once

#include <vector>

#include "common/arena.h"
#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

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
  // §16.12.2: whether strong(...) or weak(...) was written around the
  // sequence, which alone keeps the statement from choosing its strength.
  bool strength_written = false;
};

// §16.12 to §16.12.6: the parse of the property_spec of a concurrent
// assertion in the forms the evaluation reads, after its clock: the disable
// condition, and a boolean, a sequential property or a property of operands
// under not, or, and, if-else, case, implication, followed-by, implies,
// iff, nexttime, always, until, eventually and the aborts. A
// friend of Parser, defined in src/parser/parser_property_spec.cpp, for
// the event actuals in src/parser/parser_event_actual.cpp, and for the
// expression_or_dist in src/parser/parser_property_dist.cpp.
struct ParserPropertySpecHelpers {
  static Expr* PropertySpecPlaceholder(Arena& arena, SourceLoc loc);
  static ModuleItem* TryParseSequenceSpec(Parser& p, bool& strong,
                                          bool& written, bool term);
  static bool AtSpecScanEnd(Parser& p);
  static bool AheadHolds(Parser& p, TokenKind wanted, bool to_junction);
  static bool BodyHasPropertyJunction(Parser& p);
  static bool AheadOpensKeywordTerm(Parser& p);
  static bool AheadHoldsRepetition(Parser& p);
  static bool AheadHoldsSequenceOperator(Parser& p);
  static PropertyExprNode* NewPropertyNode(Parser& p,
                                           PropertyExprNode::Kind kind);
  static bool OpensPropertyGroup(Parser& p);
  static PropertyExprNode* TryParsePropertyGroup(Parser& p, bool& group);
  static Expr* ParseEventActualOperand(Parser& p);
  static Expr* ParseEventActual(Parser& p);
  static bool AheadListsNamesOnly(Parser& p);
  static Expr* ParseListedNamesActual(Parser& p);
  static Expr* ParseWholeExpressionActual(Parser& p);
  static Expr* ParsePropertyActualArg(Parser& p, bool& plain);
  static PropertyExprNode* ParseWholeSequenceActual(Parser& p);
  static Expr* ParseFormalDefault(Parser& p);
  static DataType* ParseFormalType(Parser& p);
  static bool StartsNamedFormalType(Parser& p);
  static DataType* ParseNamedFormalType(Parser& p);
  static bool ParseNamedActualPrefix(Parser& p, Expr* call, bool& named);
  static bool ParsePropertyActualList(Parser& p, Expr* call, bool& plain);
  static Expr* TryParsePropertyInstance(Parser& p);
  static Expr* RangeOfDistItem(Parser& p, const ConstraintDistItem& item);
  static bool ParseAssertionDistItem(Parser& p, ConstraintDistItem& item,
                                     int& defaults);
  static Expr* ParseExpressionOrDist(Parser& p);
  static void CheckDistListDefaults(Parser& p);
  static void CheckSpecDistDefaults(Parser& p);
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
  // §16.10 and §16.11: the sequence_match_items after a group's
  // sequence_expr, each a local's assignment, an inc_or_dec_expression or a
  // subroutine call, and the literal 1 an inc_or_dec_expression adds or
  // subtracts. Defined in src/parser/parser_sequence_match_items.cpp.
  static Expr* OneLiteral(Parser& p);
  static bool ParseMatchItemTarget(Parser& p, SeqMatchAssign& item);
  static bool ParseIncDecMatchItem(Parser& p, SeqMatchAssign& item,
                                   bool prefix);
  static bool AheadIsSubroutineCall(Parser& p);
  static Expr* ParseAttachedCall(Parser& p);
  static bool ParseSequenceMatchItem(Parser& p, SeqMatchAssign& item);
  static bool ParseSequenceMatchItems(Parser& p,
                                      std::vector<SeqMatchAssign>& items);
  // §16.14.5: the concurrent assertion item an always procedure whose body
  // opens with one of §16.14's statements is equivalent to, or nullptr,
  // nothing consumed, where the body opens with anything else. Defined in
  // src/parser/parser_assert.cpp beside the statements.
  static ModuleItem* TryParseAlwaysConcurrentAssertion(Parser& p);
  // A.6.10 with §16.14.6: a statement opening with `restrict` in procedural
  // code, which is a procedural restrict property statement or else the
  // immediate restrict §16.2 rules out. Defined in
  // src/parser/parser_assert.cpp.
  static Stmt* ParseProceduralRestrict(Parser& p);
  // §23.9, §16.8 and §16.10: records on `item` what the text from the current
  // token to `end` reads, declares, bounds with and passes to instances,
  // leaving the lexer where it was. Defined in
  // src/parser/parser_assertion_reads.cpp.
  static void RecordAssertionReads(Parser& p, ModuleItem* item, TokenKind end);
};

}  // namespace delta
