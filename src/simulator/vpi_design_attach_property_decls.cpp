#include <algorithm>
#include <cstddef>
#include <iterator>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/packed_range.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_assertion_decls.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

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

// The data type `keyword` names alone. `keyword` is a formal's or a local
// variable's type keyword other than sequence or property, which
// kKeywordTypes holds every one of: the parser rejects chandle, the one other
// keyword it reads there, as a formal's type (§16.8) and a local variable's
// (§16.10).
DataTypeKind KeywordDataType(TokenKind keyword) {
  return std::find_if(std::begin(kKeywordTypes), std::end(kKeywordTypes),
                      [keyword](const KeywordType& entry) {
                        return entry.keyword == keyword;
                      })
      ->type;
}

// §37.51 detail 3 with §37.25: the kind of typespec a property formal declared
// with the type keyword `keyword` reaches. §16.12 adds sequence and property
// to the data types a formal may be declared with; §6.12 makes realtime a
// synonym for real.
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
    default:
      return VpiTypespecKind(KeywordDataType(keyword));
  }
}

// §37.25: the typespec the typedef `name` declares in the scopes from
// `holder` out to the instance, or else among the compilation unit's, or else
// in a package an import of the module makes it visible from; null where none
// of them declares one.
VpiObject* TypedefTypespec(const VpiObject* holder, std::string_view name,
                           const VpiPropertyDeclSite& at) {
  for (const VpiObject* scope = holder; scope != nullptr;
       scope = VpiIsInstanceType(scope->type) ? nullptr : scope->parent) {
    for (VpiObject* child : scope->children) {
      if (VpiIsTypespecType(child->type) && child->name == name) return child;
    }
  }
  auto it = at.unit_typespecs.find(name);
  return it != at.unit_typespecs.end()
             ? it->second
             : VpiImportedTypespec(name, at.imports, at.unit_typespecs);
}

// §37.25 with §37.31: a class typespec of the class `name`, hung from
// `formal`, reaching the class defn of that name a scope from the property out
// to the instance declares, where one does.
VpiObject* ClassTypespec(VpiObject* formal, std::string_view name,
                         const VpiAttachBuild& build) {
  VpiObject* typespec = build.alloc();
  typespec->type = vpiClassTypespec;
  typespec->name = build.keep(std::string(name));
  typespec->parent = formal;
  for (const VpiObject* scope = formal->parent; scope != nullptr;
       scope = VpiIsInstanceType(scope->type) ? nullptr : scope->parent) {
    for (VpiObject* child : scope->children) {
      if (child->type == vpiClassDefn && child->name == name) {
        typespec->children.push_back(child);
        return typespec;
      }
    }
  }
  return typespec;
}

// §37.51 detail 3 with §37.25: the typespec the formal `index` of `decl` is
// declared with, hung from `formal`: the one the typedef it names declares,
// which other objects of that type share (§37.17), a class typespec where it
// names a class (§16.8), or one of the type's own, reaching a range per
// packed dimension it was written with (§37.22); none for an untyped formal.
void MakeFormalTypespec(const ModuleItem& decl, size_t index, VpiObject* formal,
                        const VpiPropertyDeclSite& at,
                        const VpiAttachBuild& build) {
  const DataType* type = decl.prop_formal_types[index];
  if (type != nullptr && type->kind == DataTypeKind::kNamed) {
    VpiObject* named = TypedefTypespec(formal->parent, type->type_name, at);
    formal->children.push_back(
        named != nullptr ? named
                         : ClassTypespec(formal, type->type_name, build));
    return;
  }
  const TokenKind kKeyword = decl.prop_formal_type_kw[index];
  int kind = 0;
  if (kKeyword != TokenKind::kEof && kKeyword != TokenKind::kKwUntyped) {
    kind = FormalTypespecKind(kKeyword);
  } else if (type != nullptr) {
    kind = VpiTypespecKind(type->kind);
  }
  if (kind == 0) return;
  VpiObject* typespec = build.alloc();
  typespec->type = kind;
  typespec->parent = formal;
  formal->children.push_back(typespec);
  for (const PackedRange& dim : WrittenPackedDims(type, at.ctx)) {
    typespec->children.push_back(VpiRangeObject(typespec, dim, build));
  }
}

// §37.51: the prop formal decl the formal `index` of `decl` stands as, hung
// from `property`: named, of no direction unless it is a local variable
// argument (detail 5), reaching the typespec of the type it is declared with
// (detail 3) and the default value it declares, where it declares one,
// through vpiExpr (detail 4).
void MakePropFormal(const ModuleItem& decl, size_t index, VpiObject* property,
                    const VpiPropertyDeclSite& at, const VpiStmtBuild& with) {
  VpiObject* formal = with.build.alloc();
  formal->type = vpiPropFormalDecl;
  formal->parent = property;
  formal->name = with.build.keep(std::string(decl.prop_formals[index]));
  formal->direction = VpiPropFormalDirection(decl.prop_formal_is_local[index]);
  MakeFormalTypespec(decl, index, formal, at, with.build);
  VpiObject* value = with.expression(decl.prop_formal_defaults[index]);
  if (value != nullptr) formal->children.push_back(value);
  property->children.push_back(formal);
}

// §37.53: the vpiDirection of the formal `index` of the sequence `decl`:
// none unless it is a local variable argument, which has the direction
// §16.8.2 gives it, written or inferred, `decl` recording one per such
// argument in the order declared.
int SeqFormalDirection(const ModuleItem& decl, size_t index) {
  if (!decl.prop_formal_is_local[index]) return vpiNoDirection;
  const size_t kLocal = static_cast<size_t>(std::count(
      decl.prop_formal_is_local.begin(),
      decl.prop_formal_is_local.begin() + static_cast<std::ptrdiff_t>(index),
      true));
  switch (decl.prop_seq_local_lvar_directions[kLocal]) {
    case Direction::kOutput:
      return vpiOutput;
    case Direction::kInout:
      return vpiInout;
    default:
      return vpiInput;
  }
}

// §37.53: the seq formal decl the formal `index` of `decl` stands as, hung
// from `sequence`: named, of the direction SeqFormalDirection gives it
// (detail 4), reaching the typespec of the type it is declared with (detail
// 2) and the default value it declares, where it declares one, through
// vpiExpr (detail 3).
void MakeSeqFormal(const ModuleItem& decl, size_t index, VpiObject* sequence,
                   const VpiPropertyDeclSite& at, const VpiStmtBuild& with) {
  VpiObject* formal = with.build.alloc();
  formal->type = vpiSeqFormalDecl;
  formal->parent = sequence;
  formal->name = with.build.keep(std::string(decl.prop_formals[index]));
  formal->direction = SeqFormalDirection(decl, index);
  MakeFormalTypespec(decl, index, formal, at, with.build);
  VpiObject* value = with.expression(decl.prop_formal_defaults[index]);
  if (value != nullptr) formal->children.push_back(value);
  sequence->children.push_back(formal);
}

// §37.51 and §37.53 with §16.10: the variable the local variable `local` a
// property or a sequence declares stands as, hung from its declaration
// `declared` and named in it, of the kind its type is (§37.17), the kind the
// type name it is declared with stands for where it names one (§6.18),
// resolved in `ctx`. §37.52 detail 1 gives its value no access, so it holds
// none.
void MakeDeclaredVariable(const SeqLocalDecl& local, VpiObject* declared,
                          const SimContext& ctx, const VpiAttachBuild& build) {
  VpiObject* var = build.alloc();
  var->type =
      VpiDataTypeVariableKind(local.named_type.kind == DataTypeKind::kNamed
                                  ? DeclaredTypeKind(local.named_type, ctx)
                                  : KeywordDataType(local.type_kw));
  var->parent = declared;
  var->name = build.keep(std::string(local.name));
  var->full_name = VpiScopedFullName(declared, local.name);
  declared->children.push_back(var);
}

// The child of `scope` of `type` named `name`; null where none is.
VpiObject* ChildOfType(const VpiObject* scope, int type,
                       std::string_view name) {
  for (VpiObject* child : scope->children) {
    if (child->type == type && child->name == name) return child;
  }
  return nullptr;
}

// The scope among the children of `scope` that the prefix `prefix` of a
// property's name names: a clocking block, `cb.p` (§16.16 (b)), or an
// interface instance, `i0.p` (§16.12 with §23.6); null where it names
// neither.
VpiObject* PropertyHolderNamed(const VpiObject* scope,
                               std::string_view prefix) {
  VpiObject* block = ChildOfType(scope, vpiClockingBlock, prefix);
  return block != nullptr ? block : ChildOfType(scope, vpiInterface, prefix);
}

// §37.51 and §37.53: the declaration of `type`, a property decl or a
// sequence decl, named `name` that `from` or a scope standing around it
// declares, the nearest from a generate block instance out to the instance;
// null where none was built. A name written through a clocking block or an
// interface instance is the declaration that block or instance holds.
VpiObject* DeclAround(const VpiObject* from, int type, std::string_view name) {
  const size_t kDot = name.find('.');
  for (const VpiObject* scope = from; scope != nullptr;
       scope = VpiIsInstanceType(scope->type) ? nullptr : scope->parent) {
    VpiObject* found = kDot == std::string_view::npos
                           ? ChildOfType(scope, type, name)
                           : PropertyHolderNamed(scope, name.substr(0, kDot));
    if (found != nullptr && kDot != std::string_view::npos) {
      return ChildOfType(found, type, name.substr(kDot + 1));
    }
    if (found != nullptr) return found;
  }
  return nullptr;
}

// The typespec the formal `formal` was declared with, null for an untyped one.
const VpiObject* TypespecOf(const VpiObject* formal) {
  for (const VpiObject* child : formal->children) {
    if (VpiIsTypespecType(child->type)) return child;
  }
  return nullptr;
}

// §37.51 detail 2: the argument the actual `actual` of a property inst
// stands as, bound to a formal declared with the typespec `target`, null for
// an untyped one; null for an actual the instance leaves out. A sequence or
// property the actual writes (§16.12) is the property expr of the tree the
// parser carries it as (§37.52); §37.59 detail 4 makes the terminal `$`,
// which §16.8 admits as an actual, the unbounded constant; and a typed
// formal's typespec orders a keyed pattern (detail 6).
VpiObject* ActualArgument(const Expr* actual, const VpiObject* target,
                          const VpiStmtBuild& with) {
  if (actual == nullptr) return nullptr;
  if (actual->property_actual != nullptr) {
    return VpiPropertyExprObject(actual->property_actual, with, nullptr);
  }
  if (actual->text != "$") {
    return target != nullptr ? with.assigned(actual, target)
                             : with.expression(actual);
  }
  VpiObject* dollar = with.build.alloc();
  dollar->type = vpiConstant;
  dollar->const_type = vpiUnboundedConst;
  return dollar;
}

// §37.51 and §37.53 with §37.12: the declaration of `type` the property or
// sequence `declared` stands for, hung from the scope declaring it,
// `at.scope` or the clocking block it holds that declares it, named in it.
VpiObject* MakeDeclHead(const RtlirAssertionItemDecl& declared, int type,
                        const VpiPropertyDeclSite& at,
                        const VpiAttachBuild& build) {
  VpiObject* scope = at.scope;
  // §37.12 with §14.3: a declaration a clocking block holds is of that block,
  // which AttachClockingBlocks has made under the same scope, the generate
  // block instance both are stamped with or the instance.
  if (declared.clocking_block != nullptr) {
    scope = ChildOfType(scope, vpiClockingBlock, declared.clocking_block->name);
  }
  const ModuleItem& decl = *declared.item;
  VpiObject* obj = build.alloc();
  obj->type = type;
  obj->parent = scope;
  // §16.16 (b): the run keys a clocking block's declaration under the block's
  // name and its own, `cb.p`, the block being its scope here.
  const std::string_view kName =
      declared.clocking_block == nullptr
          ? decl.name
          : decl.name.substr(decl.name.rfind('.') + 1);
  obj->name = build.keep(std::string(kName));
  obj->full_name = VpiScopedFullName(scope, kName);
  scope->children.push_back(obj);
  return obj;
}

// §26.3: the declaration of `type` named `name` a package declares that one
// of `imports` makes visible. The first import naming it, the module's own
// or, ahead of them, the compilation unit's (§3.12.1), gives it. §26.7: the
// std package every scope imports has no object of its own.
VpiObject* ImportedDecl(int type, std::string_view name,
                        const std::vector<RtlirImport>& imports,
                        const VpiObjectMap& objects) {
  VpiObject* found = nullptr;
  for (const RtlirImport& imported : imports) {
    if (found != nullptr ||
        (!imported.is_wildcard && imported.item_name != name)) {
      continue;
    }
    const VpiObject* pkg =
        FindObjectForFlatName(objects, imported.package_name);
    found = pkg != nullptr ? ChildOfType(pkg, type, name) : nullptr;
  }
  return found;
}

// §37.53 with §37.56: the sequence the body of `decl` is, built through
// `with`: a multiclock sequence expr where its operands name clocks, the
// clock the body opens with flowing into its first run, and otherwise the
// sequence expr it is, under a clocked seq of a multiclock sequence expr of
// its own where the body opens with a clock, which no sequence expr reaches;
// null where the parser read no body of the shapes §37.54 builds.
VpiObject* SequenceDeclBody(const ModuleItem& decl, const VpiStmtBuild& with) {
  VpiObject* body =
      VpiSequenceExprObject(decl.seq_linear, with, &decl.seq_clock);
  if (body == nullptr || decl.seq_clock.empty() ||
      body->type == vpiMulticlockSequenceExpr) {
    return body;
  }
  VpiObject* multiclock = with.build.alloc();
  multiclock->type = vpiMulticlockSequenceExpr;
  VpiObject* clocked = with.build.alloc();
  clocked->type = vpiClockedSeq;
  clocked->parent = multiclock;
  clocked->clocking_event = VpiEventCondition(decl.seq_clock, with);
  clocked->children.push_back(body);
  multiclock->children.push_back(clocked);
  return multiclock;
}

// §37.54: the sequence inst `instance`, a name or a call naming the sequence
// `decl` declares, writes, reaching `decl` and an argument per formal of it
// in the order declared, each built through `with` (detail 1).
VpiObject* MakeSequenceInst(VpiObject* decl, const Expr& instance,
                            const VpiStmtBuild& with) {
  VpiObject* inst = with.build.alloc();
  inst->type = vpiSequenceInst;
  inst->sequence_decl = decl;
  // §37.54 detail 1: an argument per formal, in the order declared, the
  // formal's default standing for an actual the instance leaves out. One that
  // stands for no object, an actual not modelled, the vpiArgument iteration
  // passes over.
  const std::vector<VpiHandle> kFormals = VpiSeqFormals(decl);
  std::vector<VpiHandle> provided;
  std::vector<VpiSequenceFormal> formals;
  formals.reserve(kFormals.size());
  for (std::size_t i = 0; i < kFormals.size(); ++i) {
    const Expr* actual = i < instance.args.size() ? instance.args[i] : nullptr;
    provided.push_back(ActualArgument(actual, TypespecOf(kFormals[i]), with));
    formals.push_back(VpiSequenceFormal{VpiSeqFormalInitExpr(kFormals[i])});
  }
  inst->arguments = VpiSequenceInstArguments(formals, provided);
  return inst;
}

// §37.51 and §37.54: the declaration of `type` the operand `operand` names,
// written bare, `s`, called, `s(a)`, or through a package's path, `pk::s` or
// `pk::s(a)`, which is how elaboration writes the names a package's own
// sequences and properties read (§26.3); null where it names none.
VpiObject* NamedDecl(const Expr& operand, int type, const VpiStmtBuild& with) {
  switch (operand.kind) {
    case ExprKind::kIdentifier:
      return with.assertion_decl(type, {}, operand.text);
    case ExprKind::kCall:
      return operand.callee.empty()
                 ? NamedDecl(*operand.lhs, type, with)
                 : with.assertion_decl(type, {}, operand.callee);
    case ExprKind::kMemberAccess:
      return operand.is_scope_resolution
                 ? with.assertion_decl(type, operand.lhs->text,
                                       operand.rhs->text)
                 : nullptr;
    default:
      return nullptr;
  }
}

// §37.51: the property inst `instance`, a name or a call naming the property
// `decl` declares, writes, reaching `decl` and an argument per formal of it in
// the order declared, the formal's default standing for an actual the
// instance leaves out (detail 2); with no declaration built, the actuals as
// written.
VpiObject* PropertyInstOf(VpiObject* decl, const Expr& instance,
                          const VpiStmtBuild& with) {
  VpiObject* inst = with.build.alloc();
  inst->type = vpiPropertyInst;
  inst->property_decl = decl;
  const std::vector<VpiHandle> kFormals = VpiPropFormals(decl);
  std::vector<const VpiObject*> targets(instance.args.size(), nullptr);
  for (std::size_t i = 0; i < std::min(targets.size(), kFormals.size()); ++i) {
    targets[i] = TypespecOf(kFormals[i]);
  }
  std::vector<VpiHandle> provided;
  provided.reserve(instance.args.size());
  for (std::size_t i = 0; i < instance.args.size(); ++i) {
    provided.push_back(ActualArgument(instance.args[i], targets[i], with));
  }
  std::vector<VpiPropertyFormal> formals;
  formals.reserve(kFormals.size());
  for (VpiHandle formal : kFormals) {
    formals.push_back(VpiPropertyFormal{VpiPropFormalInitExpr(formal)});
  }
  for (VpiHandle argument : formals.empty()
                                ? provided
                                : VpiPropertyInstArguments(formals, provided)) {
    if (argument != nullptr) inst->arguments.push_back(argument);
  }
  return inst;
}

}  // namespace

VpiObject* VpiMakePropertyInst(VpiObject* holder, const Expr& instance,
                               const Expr* disable, const VpiStmtBuild& with) {
  VpiObject* inst = PropertyInstOf(NamedDecl(instance, vpiPropertyDecl, with),
                                   instance, with);
  inst->parent = holder;
  // §37.51 with §16.15: the condition the instance is disabled under, the one
  // its property declares or else the default disable iff in scope.
  inst->disable_condition = with.expression(disable);
  holder->children.push_back(inst);
  return inst;
}

VpiObject* VpiPropertyOperandObject(const Expr& operand,
                                    const VpiStmtBuild& with) {
  VpiObject* decl = NamedDecl(operand, vpiPropertyDecl, with);
  return decl != nullptr ? PropertyInstOf(decl, operand, with)
                         : VpiSequenceOperandObject(operand, with);
}

VpiObject* VpiAssertionDeclNamed(const VpiAssertionDeclName& named,
                                 const std::vector<RtlirImport>& imports,
                                 const VpiObjectMap& objects) {
  // §26.3: a name written through a package's path, `pk::s`, is the one that
  // package declares, as an import of it would make it visible.
  if (!named.package.empty()) {
    RtlirImport path;
    path.package_name = named.package;
    path.item_name = named.name;
    return ImportedDecl(named.type, named.name, {path}, objects);
  }
  VpiObject* declared = DeclAround(named.scope, named.type, named.name);
  return declared != nullptr
             ? declared
             : ImportedDecl(named.type, named.name, imports, objects);
}

VpiObject* VpiSequenceOperandObject(const Expr& operand,
                                    const VpiStmtBuild& with) {
  VpiObject* decl = NamedDecl(operand, vpiSequenceDecl, with);
  return decl != nullptr ? MakeSequenceInst(decl, operand, with)
                         : with.expression(&operand);
}

void AttachPackageAssertionItemDecls(const RtlirDesign& design,
                                     const VpiObjectMap& objects,
                                     const VpiObjectMap& unit_typespecs,
                                     SimContext& ctx,
                                     const VpiAttachBuild& build) {
  // §16.8 and §16.12 with §37.10 detail 1: a sequence or a property a package
  // declares is a sequence decl or a property decl of the package, its
  // expressions resolving among the package's names, and a sequence or a
  // property it names among the package's.
  const std::vector<RtlirImport> kNoImports;
  const std::vector<std::string_view> kNoGenBlocks;
  for (const PackageDecl* pkg : design.packages) {
    const std::string kPrefix(pkg->name);
    VpiObject* package = FindObjectForFlatName(objects, pkg->name);
    // §37.42: a call a declaration makes stands in the package.
    const VpiCallStand kStand{package, nullptr, pkg->name};
    // §37.83: an operation carries the attributes its operator is written
    // with, which elaboration kept for a package's items on the design.
    const VpiExprNames kNames{
        objects, kPrefix, kNoGenBlocks, nullptr, &design.node_attrs, &kStand};
    const VpiStmtBuild kWith{
        build,
        [&](const Expr* expr) {
          return VpiGenBlockExpression(expr, kNames, ctx, build);
        },
        nullptr,
        nullptr,
        nullptr,
        [&](int type, std::string_view path, std::string_view name) {
          return VpiAssertionDeclNamed({package, type, path, name}, kNoImports,
                                       objects);
        }};
    const VpiPropertyDeclSite kAt{package, unit_typespecs, ctx, kNoImports};
    // §16.8 and §16.12: a sequence or a property may name one the package
    // declares after it, so each is declared before any body is built.
    std::vector<std::pair<VpiObject*, const ModuleItem*>> made;
    for (const ModuleItem* item : pkg->items) {
      const RtlirAssertionItemDecl kDeclared{item, {}, {}, nullptr};
      if (item->kind == ModuleItemKind::kSequenceDecl) {
        made.emplace_back(VpiMakeSequenceDecl(kDeclared, kAt, kWith), item);
      } else if (item->kind == ModuleItemKind::kPropertyDecl) {
        made.emplace_back(VpiMakePropertyDecl(kDeclared, kAt, kWith), item);
      }
    }
    for (const auto& [declared, item] : made) {
      VpiFillAssertionItemDeclBody(declared, *item, kWith);
    }
  }
}

VpiObject* VpiMakePropertyDecl(const RtlirAssertionItemDecl& declared,
                               const VpiPropertyDeclSite& at,
                               const VpiStmtBuild& with) {
  const ModuleItem& decl = *declared.item;
  VpiObject* obj = MakeDeclHead(declared, vpiPropertyDecl, at, with.build);
  for (size_t i = 0; i < decl.prop_formals.size(); ++i) {
    MakePropFormal(decl, i, obj, at, with);
  }
  for (const SeqLocalDecl& local : decl.prop_locals) {
    MakeDeclaredVariable(local, obj, at.ctx, with.build);
  }
  return obj;
}

VpiObject* VpiMakeSequenceDecl(const RtlirAssertionItemDecl& declared,
                               const VpiPropertyDeclSite& at,
                               const VpiStmtBuild& with) {
  const ModuleItem& decl = *declared.item;
  VpiObject* obj = MakeDeclHead(declared, vpiSequenceDecl, at, with.build);
  for (size_t i = 0; i < decl.prop_formals.size(); ++i) {
    MakeSeqFormal(decl, i, obj, at, with);
  }
  for (const SeqLocalDecl& local : decl.seq_linear.locals) {
    MakeDeclaredVariable(local, obj, at.ctx, with.build);
  }
  return obj;
}

void VpiFillAssertionItemDeclBody(VpiObject* made, const ModuleItem& decl,
                                  const VpiStmtBuild& with) {
  if (made->type == vpiSequenceDecl) {
    made->body = SequenceDeclBody(decl, with);
    return;
  }
  // §37.52: the body the parser read, its clock, its disable condition and,
  // for a Boolean property, its expression; a body of another shape was not
  // read and stands for no spec.
  const PropertyExprNode* tree = decl.prop_body_tree;
  if (tree == nullptr) return;
  VpiMakePropertySpecOf(
      made, VpiPropertySpecParts{decl.prop_clock, decl.prop_disable_iff, tree},
      with);
}

}  // namespace delta
