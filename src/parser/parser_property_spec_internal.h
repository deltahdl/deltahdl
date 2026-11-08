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

struct SimpleSpecBody {
  Expr* disable_iff = nullptr;
  Expr* prop = nullptr;
  ModuleItem* sequence = nullptr;
  bool strong = false;
  bool negated = false;
  PropertyExprNode* property = nullptr;
  bool strength_written = false;
};

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
  static bool ParsePropertyLocalDecls(Parser& p,
                                      std::vector<SeqLocalDecl>& locals);
  static Expr* OneLiteral(Parser& p);
  static bool ParseMatchItemTarget(Parser& p, SeqMatchAssign& item);
  static bool ParseIncDecMatchItem(Parser& p, SeqMatchAssign& item,
                                   bool prefix);
  static bool AheadIsSubroutineCall(Parser& p);
  static Expr* ParseAttachedCall(Parser& p);
  static bool ParseSequenceMatchItem(Parser& p, SeqMatchAssign& item);
  static bool ParseSequenceMatchItems(Parser& p,
                                      std::vector<SeqMatchAssign>& items);
  static ModuleItem* TryParseAlwaysConcurrentAssertion(Parser& p);
  static Stmt* ParseProceduralRestrict(Parser& p);
  static void RecordAssertionReads(Parser& p, ModuleItem* item, TokenKind end);
};

}  // namespace delta
