#pragma once

#include <initializer_list>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/source_loc.h"
#include "elaborator/value_scopes.h"

namespace delta {

struct Attribute;
struct BinsOrOptions;
struct BindDirective;
struct ClassDecl;
struct CompilationUnit;
struct ConstraintDistItem;
struct ConstraintItem;
struct CoverCrossDecl;
struct CovergroupDecl;
struct CovergroupValueRange;
struct DataType;
struct EventExpr;
struct Expr;
struct FunctionArg;
struct ModuleDecl;
struct ModuleItem;
struct PropertyExprNode;
struct SelectExpression;
struct SeqCycleDelay;
struct SeqLinearBody;
struct SeqLocalDecl;
struct SeqMatchAssign;
struct SpecifyItem;
struct SpecifyTerminal;
struct Stmt;

class ScopedWalk {
 public:
  explicit ScopedWalk(const CompilationUnit& unit) : scopes_(unit) {}

  virtual ~ScopedWalk() = default;

  ScopedWalk(const ScopedWalk&) = delete;

  ScopedWalk& operator=(const ScopedWalk&) = delete;

  void WalkUnit(const CompilationUnit& unit);

 protected:
  virtual void VisitExpr(const Expr& e, const NameScope& scope) = 0;

  virtual void VisitType(const DataType& type, SourceLoc loc,
                         const NameScope& scope) = 0;

  virtual void VisitClass(const ClassDecl& cls, const NameScope& scope) = 0;

  virtual void VisitRange(const Expr&, const NameScope&) {}

  virtual void VisitModule(const ModuleDecl&, const NameScope&) {}

  virtual void VisitParameter(const ModuleItem&, const NameScope&) {}

  virtual void VisitInstance(const ModuleItem&, const NameScope&) {}

  const ValueScopes& Scopes() const { return scopes_; }

 private:
  void WalkExprs(const std::vector<Expr*>& exprs, const NameScope& scope);

  void WalkEach(std::initializer_list<const Expr*> exprs,
                const NameScope& scope);

  void WalkAttributes(const std::vector<Attribute>& attrs,
                      const NameScope& scope);

  void WalkRanges(const std::vector<Expr*>& bounds, const NameScope& scope);

  void VisitRanges(const std::vector<Expr*>& bounds, const NameScope& scope);

  void WalkParamPorts(
      const std::unordered_map<std::string_view, std::vector<Expr*>>& dims,
      const NameScope& scope);

  void WalkWith(const Expr& call, const NameScope& scope);

  void WalkInlineConstraint(const Expr& call, const NameScope& scope);

  void WalkExpr(const Expr* e, const NameScope& scope);

  void WalkDist(const std::vector<ConstraintDistItem>& items,
                const NameScope& scope);

  void WalkConstraints(const std::vector<ConstraintItem*>& items,
                       const NameScope& scope);

  void WalkEvents(const std::vector<EventExpr>& events, const NameScope& scope);

  void WalkDelay(const SeqCycleDelay& delay, const NameScope& scope);

  void WalkTargets(const std::vector<SeqMatchAssign>& items,
                   const NameScope& scope);

  void WalkLocals(const std::vector<SeqLocalDecl>& locals, SourceLoc loc,
                  NameScope& scope);

  void WalkSequence(const SeqLinearBody& body, const NameScope& scope);

  void WalkTree(const PropertyExprNode* tree, const NameScope& scope);

  void WalkType(const DataType& type, SourceLoc loc, const NameScope& scope);

  void VisitTypeRanges(const DataType& type, const NameScope& scope);

  void WalkDeclaredType(const DataType& type, SourceLoc loc,
                        const NameScope& scope);

  void WalkTypes(const std::vector<DataType>& types, SourceLoc loc,
                 const NameScope& scope);

  void WalkDeclaredTypes(const std::vector<DataType>& types, SourceLoc loc,
                         const NameScope& scope);

  void WalkHeader(const ClassDecl& cls, const NameScope& scope);

  void DeclareLoopNames(const Stmt& stmt, NameScope& scope);

  void WalkStmt(const Stmt* stmt, const NameScope& outer);

  void WalkFormals(const std::vector<FunctionArg>& formals, SourceLoc loc,
                   const NameScope& scope);

  void WalkBody(const ModuleItem& item, const NameScope& outer);

  void WalkSubroutine(const ModuleItem& item, const NameScope& scope);

  void WalkPropertyOrSequence(const ModuleItem& item, const NameScope& outer);

  void WalkValueRanges(const std::vector<CovergroupValueRange>& ranges,
                       const NameScope& scope);

  void WalkBins(const BinsOrOptions& bins, const NameScope& scope);

  void WalkBinsSelection(const SelectExpression* select,
                         const NameScope& scope);

  void WalkCross(const CoverCrossDecl& cross, const NameScope& scope);

  void WalkCovergroup(const CovergroupDecl& group, SourceLoc loc,
                      const NameScope& outer);

  void WalkClass(const ClassDecl& cls);

  void WalkGenerate(const ModuleItem& item, const NameScope& outer);

  void WalkGenerateBlock(const std::vector<ModuleItem*>& items,
                         const NameScope& outer);

  void WalkInstance(const ModuleItem& item, const NameScope& scope);

  void WalkBind(const BindDirective& bind);

  void WalkClocking(const ModuleItem& item, const NameScope& scope);

  void WalkSpecify(const SpecifyItem& item, const NameScope& scope);

  void WalkTerminals(const std::vector<SpecifyTerminal>& terminals,
                     const NameScope& scope);

  void WalkItem(const ModuleItem& item, const NameScope& scope);

  void WalkItems(const std::vector<ModuleItem*>& items, const NameScope& scope);

  void WalkModule(const ModuleDecl& decl);

  ValueScopes scopes_;
};

}  // namespace delta
