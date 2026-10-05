#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/source_mgr.h"
#include "elaborator/rtlir_scopes.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"

namespace delta {

namespace {

// §37.50: the object kind of the concurrent assertion `item` writes, by its
// keyword.
int ConcurrentKindOf(const ModuleItem& item) {
  switch (item.kind) {
    case ModuleItemKind::kAssumeProperty:
      return vpiAssume;
    case ModuleItemKind::kCoverProperty:
    case ModuleItemKind::kCoverSequence:
      return vpiCover;
    case ModuleItemKind::kRestrictProperty:
      return vpiRestrict;
    default:
      return vpiAssert;
  }
}

// §37.50: the object the concurrent assertion `item` stands as in `scope`,
// named by its label, reporting where it stands and, for a cover, whether it
// covers a sequence.
VpiObject* MakeConcurrentAssertion(const ModuleItem& item, VpiObject* scope,
                                   SimContext& ctx,
                                   const VpiAttachBuild& build) {
  VpiObject* obj = build.alloc();
  obj->type = ConcurrentKindOf(item);
  obj->parent = scope;
  if (!item.name.empty()) {
    obj->name = build.keep(std::string(item.name));
    obj->full_name = VpiScopedFullName(scope, item.name);
  }
  obj->cover_sequence = item.kind == ModuleItemKind::kCoverSequence;
  VpiRecordAssertionLocation(obj, SourceRange{item.loc, item.end}, ctx);
  scope->children.push_back(obj);
  return obj;
}

// §6.11, §6.12 and §6.17: the data type a type keyword names alone.
struct KeywordType {
  TokenKind keyword;
  DataTypeKind type;
};
constexpr KeywordType kKeywordTypes[] = {
    {TokenKind::kKwLogic, DataTypeKind::kLogic},
    {TokenKind::kKwReg, DataTypeKind::kReg},
    {TokenKind::kKwBit, DataTypeKind::kBit},
    {TokenKind::kKwByte, DataTypeKind::kByte},
    {TokenKind::kKwShortint, DataTypeKind::kShortint},
    {TokenKind::kKwInt, DataTypeKind::kInt},
    {TokenKind::kKwLongint, DataTypeKind::kLongint},
    {TokenKind::kKwInteger, DataTypeKind::kInteger},
    {TokenKind::kKwTime, DataTypeKind::kTime},
    {TokenKind::kKwReal, DataTypeKind::kReal},
    {TokenKind::kKwShortreal, DataTypeKind::kShortreal},
    {TokenKind::kKwRealtime, DataTypeKind::kRealtime},
    {TokenKind::kKwString, DataTypeKind::kString},
    {TokenKind::kKwEvent, DataTypeKind::kEvent},
};

// The data type `keyword` names alone; kImplicit where it names none.
DataTypeKind KeywordDataType(TokenKind keyword) {
  for (const KeywordType& entry : kKeywordTypes) {
    if (entry.keyword == keyword) return entry.type;
  }
  return DataTypeKind::kImplicit;
}

// §37.51 detail 3 with §37.25: the kind of typespec a property formal declared
// with the type keyword `keyword` reaches, 0 for an untyped formal, which
// reaches none. §16.12 adds sequence and property to the data types a formal
// may be declared with; §6.12 makes realtime a synonym for real.
int FormalTypespecKind(TokenKind keyword) {
  switch (keyword) {
    case TokenKind::kKwSequence:
      return vpiSequenceTypespec;
    case TokenKind::kKwProperty:
      return vpiPropertyTypespec;
    case TokenKind::kKwEvent:
      return vpiEventTypespec;
    case TokenKind::kKwRealtime:
      return vpiRealTypespec;
    default: {
      const DataTypeKind kType = KeywordDataType(keyword);
      return kType == DataTypeKind::kImplicit ? 0 : VpiTypespecKind(kType);
    }
  }
}

// §37.51: the prop formal decl the formal `index` of `decl` stands as, hung
// from `property`: named, of no direction unless it is a local variable
// argument (detail 5), reaching the typespec of the type it is declared with
// (detail 3) and the default value it declares, where it declares one,
// through vpiExpr (detail 4).
void MakePropFormal(const ModuleItem& decl, size_t index, VpiObject* property,
                    const VpiStmtBuild& with) {
  VpiObject* formal = with.build.alloc();
  formal->type = vpiPropFormalDecl;
  formal->parent = property;
  formal->name = with.build.keep(std::string(decl.prop_formals[index]));
  formal->direction =
      VpiPropFormalDirection(index < decl.prop_formal_is_local.size() &&
                             decl.prop_formal_is_local[index]);
  const int kTypespec =
      index < decl.prop_formal_type_kw.size()
          ? FormalTypespecKind(decl.prop_formal_type_kw[index])
          : 0;
  if (kTypespec != 0) {
    VpiObject* typespec = with.build.alloc();
    typespec->type = kTypespec;
    typespec->parent = formal;
    formal->children.push_back(typespec);
  }
  if (index < decl.prop_formal_defaults.size()) {
    VpiObject* value = with.expression(decl.prop_formal_defaults[index]);
    if (value != nullptr) formal->children.push_back(value);
  }
  property->children.push_back(formal);
}

// §37.51 with §16.10: the variable the local variable `local` a property
// declares stands as, hung from the property decl `property` and named in
// it, of the kind its type is (§37.17). §37.52 detail 1 gives its value no
// access, so it holds none.
void MakePropertyVariable(const SeqLocalDecl& local, VpiObject* property,
                          const VpiAttachBuild& build) {
  VpiObject* var = build.alloc();
  var->type = VpiDataTypeVariableKind(KeywordDataType(local.type_kw));
  var->parent = property;
  var->name = build.keep(std::string(local.name));
  var->full_name = VpiScopedFullName(property, local.name);
  property->children.push_back(var);
}

// The child of `scope` of `type` named `name`; null where none is.
VpiObject* ChildOfType(const VpiObject* scope, int type,
                       std::string_view name) {
  for (VpiObject* child : scope->children) {
    if (child->type == type && child->name == name) return child;
  }
  return nullptr;
}

// §37.51: the property decl named `name` the scope standing around `holder`
// declares, the nearest from a generate block instance out to the instance;
// null where none was built. §16.16 (b): a name written through a clocking
// block, `cb.p`, is the property that block declares.
VpiObject* PropertyDeclAround(const VpiObject* holder, std::string_view name) {
  const size_t kDot = name.find('.');
  for (VpiObject* scope = holder->parent; scope != nullptr;
       scope = scope->parent) {
    VpiObject* found =
        kDot == std::string_view::npos
            ? ChildOfType(scope, vpiPropertyDecl, name)
            : ChildOfType(scope, vpiClockingBlock, name.substr(0, kDot));
    if (found != nullptr && kDot != std::string_view::npos) {
      return ChildOfType(found, vpiPropertyDecl, name.substr(kDot + 1));
    }
    if (found != nullptr) return found;
    if (VpiIsInstanceType(scope->type)) break;
  }
  return nullptr;
}

}  // namespace

VpiObject* VpiMakePropertyInst(VpiObject* holder, const Expr& instance,
                               const VpiStmtBuild& with) {
  VpiObject* inst = with.build.alloc();
  inst->type = vpiPropertyInst;
  inst->parent = holder;
  const std::string_view kName =
      instance.kind == ExprKind::kCall ? instance.callee : instance.text;
  inst->property_decl = PropertyDeclAround(holder, kName);
  // §37.51 detail 2: an argument per formal, in the order declared, the
  // formal's default standing for an actual the instance leaves out; with no
  // declaration built, the actuals as written.
  std::vector<VpiHandle> provided;
  provided.reserve(instance.args.size());
  for (const Expr* actual : instance.args) {
    provided.push_back(with.expression(actual));
  }
  std::vector<VpiPropertyFormal> formals;
  for (VpiHandle formal : VpiPropFormals(inst->property_decl)) {
    formals.push_back(VpiPropertyFormal{VpiPropFormalInitExpr(formal)});
  }
  for (VpiHandle argument : formals.empty()
                                ? provided
                                : VpiPropertyInstArguments(formals, provided)) {
    if (argument != nullptr) inst->arguments.push_back(argument);
  }
  holder->children.push_back(inst);
  return inst;
}

VpiObject* VpiMakePropertyDecl(const RtlirPropertyDecl& declared,
                               VpiObject* scope, const VpiStmtBuild& with) {
  // §37.12 with §14.3: a property a clocking block declares is of that block.
  if (declared.clocking_block != nullptr) {
    scope = ChildOfType(scope, vpiClockingBlock, declared.clocking_block->name);
    if (scope == nullptr) return nullptr;
  }
  const ModuleItem& decl = *declared.item;
  VpiObject* obj = with.build.alloc();
  obj->type = vpiPropertyDecl;
  obj->parent = scope;
  // §16.16 (b): the run keys a clocking block's property under the block's
  // name and its own, `cb.p`, the block being its scope here.
  const std::string_view kName =
      declared.clocking_block == nullptr
          ? decl.name
          : decl.name.substr(decl.name.rfind('.') + 1);
  obj->name = with.build.keep(std::string(kName));
  obj->full_name = VpiScopedFullName(scope, kName);
  scope->children.push_back(obj);
  for (size_t i = 0; i < decl.prop_formals.size(); ++i) {
    MakePropFormal(decl, i, obj, with);
  }
  for (const SeqLocalDecl& local : decl.prop_locals) {
    MakePropertyVariable(local, obj, with.build);
  }
  // §37.52: the body the parser read, its clock, its disable condition and,
  // for a Boolean property, its expression; a body of another shape was not
  // read and stands for no spec.
  const PropertyExprNode* tree = decl.prop_body_tree;
  if (tree == nullptr) return obj;
  const bool kBoolean = tree->kind == PropertyExprNode::Kind::kBoolean;
  VpiMakePropertySpecOf(
      obj,
      VpiPropertySpecParts{decl.prop_clock, decl.prop_disable_iff,
                           kBoolean ? tree->boolean : nullptr},
      with);
  return obj;
}

void VpiRecordAssertionLocation(VpiObject* obj, const SourceRange& range,
                                SimContext& ctx) {
  // §37.49: where the assertion stands - its file, the line and column it
  // starts at and those it ends at - read where the text was written (§22.12).
  // A position the parser did not record leaves its pair as it was.
  const SourceManager& sources = ctx.GetDiag().Sources();
  if (range.start.IsValid()) {
    const SourceLoc kStart = sources.ResolveToOrigin(range.start);
    obj->file = std::string(sources.FilePath(kStart.file_id));
    obj->start_line = static_cast<int>(kStart.line);
    obj->column = static_cast<int>(kStart.column);
  }
  if (range.end.IsValid()) {
    const SourceLoc kEnd = sources.ResolveToOrigin(range.end);
    obj->end_line = static_cast<int>(kEnd.line);
    obj->end_column = static_cast<int>(kEnd.column);
  }
}

void VpiMakeItemAssertion(const RtlirAssertion& assertion, VpiObject* scope,
                          SimContext& ctx, const VpiStmtBuild& with) {
  const ModuleItem& item = *assertion.item;
  // §37.49 with §39.3.1 step b: an assertion written as an item is an
  // assertion of the scope writing it. A deferred immediate one runs as a
  // process the elaborator makes of it, whose walk builds it as the statement
  // it is, with its parts (§37.55).
  if (item.body != nullptr && item.body->is_deferred) return;
  VpiObject* obj = MakeConcurrentAssertion(item, scope, ctx, with.build);
  // §37.50: the clock the elaborator resolved onto the statement it carries,
  // where it carries one, and the property: a property inst where the spec
  // instantiates a declared property, a property spec otherwise.
  if (item.body != nullptr) {
    VpiFillAssertionClock(obj, *item.body, with);
    // §16.5.2: a clock of $global_clock is the event this instance's global
    // clocking declaration names (§14.14).
    if (assertion.leading_clock != nullptr) {
      obj->clocking_event = VpiEventCondition(*assertion.leading_clock, with);
    }
  }
  if (!item.prop_instance_name.empty() && item.assert_expr != nullptr) {
    VpiMakePropertyInst(obj, *item.assert_expr, with);
  } else if (item.body != nullptr) {
    VpiMakePropertySpec(obj, *item.body, with);
  }
  // §37.50 detail 2: a restrict writes no action; §16.14.3 gives a cover a
  // pass action alone.
  with.statement(item.assert_pass_stmt, obj);
  obj->else_stmt = with.statement(item.assert_fail_stmt, obj);
}

}  // namespace delta
