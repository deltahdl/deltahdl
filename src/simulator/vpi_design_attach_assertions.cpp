#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/source_mgr.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
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

// §37.51: the prop formal decl the formal `index` of `decl` stands as, hung
// from `property`: named, of no direction unless it is a local variable
// argument (detail 5), and reaching the default value it declares, where it
// declares one, through vpiExpr (detail 4).
void MakePropFormal(const ModuleItem& decl, size_t index, VpiObject* property,
                    const VpiStmtBuild& with) {
  VpiObject* formal = with.build.alloc();
  formal->type = vpiPropFormalDecl;
  formal->parent = property;
  formal->name = with.build.keep(std::string(decl.prop_formals[index]));
  formal->direction =
      VpiPropFormalDirection(index < decl.prop_formal_is_local.size() &&
                             decl.prop_formal_is_local[index]);
  if (index < decl.prop_formal_defaults.size()) {
    VpiObject* value = with.expression(decl.prop_formal_defaults[index]);
    if (value != nullptr) formal->children.push_back(value);
  }
  property->children.push_back(formal);
}

// §37.51: the property decl named `name` the scope standing around `holder`
// declares, the nearest from a generate block instance out to the instance;
// null where none was built.
VpiObject* PropertyDeclAround(const VpiObject* holder, std::string_view name) {
  for (VpiObject* scope = holder->parent; scope != nullptr;
       scope = scope->parent) {
    for (VpiObject* child : scope->children) {
      if (child->type == vpiPropertyDecl && child->name == name) return child;
    }
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

VpiObject* VpiMakePropertyDecl(const ModuleItem& decl, VpiObject* scope,
                               const VpiStmtBuild& with) {
  VpiObject* obj = with.build.alloc();
  obj->type = vpiPropertyDecl;
  obj->parent = scope;
  obj->name = with.build.keep(std::string(decl.name));
  obj->full_name = VpiScopedFullName(scope, decl.name);
  scope->children.push_back(obj);
  for (size_t i = 0; i < decl.prop_formals.size(); ++i) {
    MakePropFormal(decl, i, obj, with);
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
