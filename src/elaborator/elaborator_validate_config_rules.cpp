#include <algorithm>
#include <cstdint>
#include <format>
#include <functional>
#include <initializer_list>
#include <optional>
#include <string>
#include <string_view>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/assertion_body_slots.h"
#include "elaborator/assertion_walk.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_modport_imports.h"
#include "elaborator/elaborator_scope_rules_names.h"
#include "elaborator/elaborator_validate_classes_internal.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/std_package.h"
#include "elaborator/type_eval.h"
#include "parser/ast_assertion_text.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

struct PackageRefContext {
  const CompilationUnit* unit;
  const std::unordered_set<std::string_view>* known_package_names;
  const std::unordered_set<std::string_view>* cu_top_names;
  std::unordered_set<std::string_view> pkg_names;
  std::unordered_set<std::string_view> imported_names;
  std::unordered_set<std::string_view> wildcard_pkgs;
  ProvidedNameCache* provided_names;
  DiagEngine* diag;
  // §26.2 within a class the package declares: the names of the unit's
  // design elements, the one head of a member access taken there for a
  // hierarchical reference, since a method also reads the members a base class
  // an import declares hands down (§8.13), which no name here lists. Null
  // outside a class.
  const std::unordered_set<std::string_view>* design_elements = nullptr;
};

std::unordered_set<std::string_view> CollectCuTopNames(
    const CompilationUnit* unit) {
  std::unordered_set<std::string_view> cu_top_names;
  for (const auto* item : unit->cu_items) {
    if (!item->name.empty()) cu_top_names.insert(item->name);
    if (item->kind == ModuleItemKind::kClassDecl && item->class_decl) {
      cu_top_names.insert(item->class_decl->name);
    }
  }
  for (const auto* cls : unit->classes) cu_top_names.insert(cls->name);
  return cu_top_names;
}

void CollectPackageLocalNames(const PackageDecl* pkg, PackageRefContext& ctx) {
  for (const auto* it : pkg->items) {
    if (!it->name.empty()) ctx.pkg_names.insert(it->name);
    if (it->kind == ModuleItemKind::kClassDecl && it->class_decl) {
      ctx.pkg_names.insert(it->class_decl->name);
    }
    if (it->kind == ModuleItemKind::kImportDecl) {
      if (it->import_item.is_wildcard) {
        ctx.wildcard_pkgs.insert(it->import_item.package_name);
      } else {
        ctx.imported_names.insert(it->import_item.item_name);
      }
    }
  }
}

// §26.3 (printed page 810) with §26.6 (printed 815-816): whether a wildcard
// import the package wrote makes `name` visible in it -- a declaration of
// the imported package, a constant of an enumeration it declares, or a name
// its exports hand on -- as PackageProvidesName answers the same question of
// a module's wildcard import.
bool IsProvidedByWildcard(const PackageRefContext& ctx, std::string_view name) {
  for (auto pname : ctx.wildcard_pkgs) {
    if (PackageProvidesName(ctx.unit, *ctx.provided_names, pname, name))
      return true;
  }
  return false;
}

// §26.2 (printed page 808): the names an import makes visible in the package,
// the one an explicit import names and every one a wildcard import provides.
bool IsImportedName(const PackageRefContext& ctx, std::string_view name) {
  return ctx.imported_names.count(name) != 0 || IsProvidedByWildcard(ctx, name);
}

// §26.2 (printed page 808): a package item may not refer to an item of the
// compilation-unit scope, which a name the package declares or imports hides.
void CheckPackageRefCuName(const PackageRefContext& ctx, std::string_view name,
                           SourceLoc loc) {
  if (ctx.cu_top_names->count(name) && !ctx.pkg_names.count(name) &&
      !IsImportedName(ctx, name)) {
    ctx.diag->Error(loc,
                    std::format("package item references '{}' from the "
                                "compilation-unit scope; packages cannot refer "
                                "to compilation-unit-scope items",
                                name),
                    Subclause("26.2"));
  }
}

void CheckPackageRefIdentifier(const PackageRefContext& ctx, const Expr* e) {
  if (!e->scope_prefix.empty()) {
    ctx.diag->Error(
        e->range.start,
        std::format("package item uses scope prefix '{}', which targets "
                    "a scope outside the package",
                    e->scope_prefix),
        Subclause("26.2"));
  } else {
    CheckPackageRefCuName(ctx, e->text, e->range.start);
  }
}

// §26.7 (printed pages 816-817): the built-in package std is declared in
// every compilation unit and its declarations -- Annex G's semaphore,
// mailbox, randomize, process and weak_reference (printed 1257-1258) -- are
// visible in every scope as a wildcard import makes them, and may be named
// behind the `std::` qualifier too; so `process::self()` and
// `std::process::self()` in a package function reference an imported
// package. Held to the packages the unit declares, uvm_globals.svh's
// `process::self()` was reported.
bool IsStdPackageOrMember(std::string_view name) {
  return name == "std" || StdPackageMemberNamed(name).has_value();
}

// §26.2 (printed page 808): a package item may reference a package's name
// through the scope resolution operator, the package's own declarations and
// what its imports make visible, an explicit import's one name or a wildcard
// import's every provided name (§26.3, printed 810); the head of any other
// member access is a hierarchical reference the subclause forbids. Held to
// the package's own names, `r.push_back(v)` in a function of a package with
// `import p0::*` was reported for p0's queue r.
bool RootIsOutsidePackage(const PackageRefContext& ctx, std::string_view root) {
  if (ctx.design_elements != nullptr) {
    return ctx.design_elements->count(root) != 0;
  }
  bool is_pkg =
      ctx.known_package_names->count(root) > 0 || IsStdPackageOrMember(root);
  bool is_self = ctx.pkg_names.count(root) > 0;
  return !is_pkg && !is_self && !IsImportedName(ctx, root);
}

void CheckPackageRefRoot(const PackageRefContext& ctx, std::string_view root,
                         SourceLoc loc) {
  if (RootIsOutsidePackage(ctx, root)) {
    ctx.diag->Error(loc,
                    std::format("package item contains a hierarchical "
                                "reference '{}' that does not target the "
                                "package itself or an imported package",
                                root),
                    Subclause("26.2"));
  }
}

void CheckPackageRefMemberRoot(const PackageRefContext& ctx, const Expr* e) {
  if (e->lhs && e->lhs->kind == ExprKind::kIdentifier && e->rhs) {
    CheckPackageRefRoot(ctx, e->lhs->text, e->range.start);
  }
}

void WalkPropertyNode(const PackageRefContext& ctx, PropertyExprNode* node);

// An expression of a package item, the sequence or property an operand
// stands in place of included: a parenthesized group joining sequences
// (§16.9) or a sequence or property passed as an actual (§16.8.1), which the
// parser holds as a tree of its own under `property_actual`.
void WalkPackageRefExpr(const PackageRefContext& ctx, const Expr* e) {
  if (!e) return;
  WalkPropertyNode(ctx, e->property_actual);
  if (e->kind == ExprKind::kIdentifier) {
    CheckPackageRefIdentifier(ctx, e);
  } else if (e->kind == ExprKind::kMemberAccess) {
    CheckPackageRefMemberRoot(ctx, e);
    WalkPackageRefExpr(ctx, e->lhs);
    WalkPackageRefExpr(ctx, e->base);
    WalkPackageRefExpr(ctx, e->index);
    WalkPackageRefExpr(ctx, e->index_end);
    return;
  }
  WalkPackageRefExpr(ctx, e->lhs);
  WalkPackageRefExpr(ctx, e->rhs);
  WalkPackageRefExpr(ctx, e->base);
  WalkPackageRefExpr(ctx, e->index);
  WalkPackageRefExpr(ctx, e->index_end);
  WalkPackageRefExpr(ctx, e->condition);
  WalkPackageRefExpr(ctx, e->true_expr);
  WalkPackageRefExpr(ctx, e->false_expr);
  WalkPackageRefExpr(ctx, e->repeat_count);
  WalkPackageRefExpr(ctx, e->with_expr);
  WalkPackageRefExpr(ctx, e->stream_range);
  for (const auto* a : e->args) WalkPackageRefExpr(ctx, a);
  for (const auto* el : e->elements) WalkPackageRefExpr(ctx, el);
}

// §26.2 holds for a subroutine's body as for a variable's initializer, and
// the body's own names are the subroutine's -- §6.21 makes its formals, its
// result and the declarations of the body and of each block in it visible
// there -- so a name declared under `s` joins the package's names for the
// subtree it is visible in and comes out again after it; an expression of the
// statement is then judged as an initializer is.
void WalkPackageRefStmt(PackageRefContext& ctx, const Stmt* s) {
  if (s == nullptr) return;
  std::vector<std::string_view> added;
  for (auto name : NamesDeclaredUnder(s)) {
    if (ctx.pkg_names.insert(name).second) added.push_back(name);
  }
  ForEachChildExpr(s, [&](const Expr* e) { WalkPackageRefExpr(ctx, e); });
  ForEachChildStmt(s, [&](const Stmt* sub) { WalkPackageRefStmt(ctx, sub); });
  for (auto name : added) ctx.pkg_names.erase(name);
}

// Runs `walk` with `names` joining the package's names for its length, the
// names a body sees as its own and not as the package's.
void WalkWithNames(PackageRefContext& ctx,
                   const std::unordered_set<std::string_view>& names,
                   const std::function<void()>& walk) {
  std::vector<std::string_view> added;
  for (auto name : names) {
    if (ctx.pkg_names.insert(name).second) added.push_back(name);
  }
  walk();
  for (auto name : added) ctx.pkg_names.erase(name);
}

// A subroutine's or a method's body, walked with the names the whole body sees
// added for the walk.
void WalkMethodBody(PackageRefContext& ctx, const ModuleItem* method) {
  WalkWithNames(ctx, CollectMethodLocalNames(method), [&] {
    for (const auto* s : method->func_body_stmts) WalkPackageRefStmt(ctx, s);
  });
}

// A subroutine of the package, an out-of-block class method among the items
// left to its class (§8.24, WalkPackageClass).
void WalkPackageSubroutine(PackageRefContext& ctx, const ModuleItem* item) {
  bool is_subroutine = item->kind == ModuleItemKind::kFunctionDecl ||
                       item->kind == ModuleItemKind::kTaskDecl;
  if (!is_subroutine || !item->method_class.empty()) return;
  WalkMethodBody(ctx, item);
}

// An item's initializer, and a let's body (§11.12), which reads the let's
// formals as its own names.
void WalkPackageItemInit(PackageRefContext& ctx, const ModuleItem* item) {
  if (item->init_expr == nullptr) return;
  std::unordered_set<std::string_view> formals;
  for (const FunctionArg& arg : item->func_args) formals.insert(arg.name);
  WalkWithNames(ctx, formals,
                [&] { WalkPackageRefExpr(ctx, item->init_expr); });
}

// Each expression of the property tree under `node`, the sequences of its
// operands and antecedents, its ranges, case items and operand clocks
// included.
void WalkPropertyNode(const PackageRefContext& ctx, PropertyExprNode* node) {
  if (node == nullptr) return;
  ForEachTreeSlot(node, [&](const Expr* e) { WalkPackageRefExpr(ctx, e); });
}

// §26.2 holds for a property the package declares (§16.12): its clocking
// event, its disable condition and its body, which read its formals and its
// locals as its own names.
void WalkPackageProperty(PackageRefContext& ctx, const ModuleItem* item) {
  if (item->kind != ModuleItemKind::kPropertyDecl) return;
  WalkWithNames(ctx, AssertionBoundNames(item), [&] {
    for (const EventExpr& ev : item->prop_clock) {
      WalkPackageRefExpr(ctx, ev.signal);
    }
    WalkPackageRefExpr(ctx, item->prop_disable_iff);
    WalkPackageRefExpr(ctx, item->prop_body_expr);
    WalkPropertyNode(ctx, item->prop_body_tree);
  });
}

// §26.2 for a sequence body of a shape the parser's linear form does not
// hold (§16.7), which keeps no expression: each name the body reads, as the
// parser's scan of its text records it, is judged as an identifier is, and
// one a member access starts from as that access's root is. A name of the
// clock, which is kept as an expression whatever the body's shape, is judged
// there.
void WalkPackageSequenceReads(const PackageRefContext& ctx, ModuleItem* item) {
  std::vector<SourceLoc> clock_names;
  ForEachEventSlot(item->seq_clock, [&](const Expr* slot) {
    ForEachSubExpr(slot, [&](const Expr* e) {
      if (e->kind == ExprKind::kIdentifier)
        clock_names.push_back(e->range.start);
    });
  });
  for (const AssertionRead& read : item->assertion_reads) {
    bool in_clock = std::ranges::any_of(clock_names, [&](SourceLoc loc) {
      return std::tie(loc.file_id, loc.line, loc.column) ==
             std::tie(read.loc.file_id, read.loc.line, read.loc.column);
    });
    if (in_clock) continue;
    CheckPackageRefCuName(ctx, read.name, read.loc);
    if (read.heads_member_access) CheckPackageRefRoot(ctx, read.name, read.loc);
  }
}

// §26.2 holds for a sequence the package declares (§16.8): its clocking event
// and its body, which read its formals and its locals as its own names. The
// body is the one the parser holds in seq_linear, or, where that holds none,
// the reads its scan of the text records.
void WalkPackageSequence(PackageRefContext& ctx, ModuleItem* item) {
  if (item->kind != ModuleItemKind::kSequenceDecl) return;
  auto walk = [&](const Expr* e) { WalkPackageRefExpr(ctx, e); };
  WalkWithNames(ctx, AssertionBoundNames(item), [&] {
    ForEachEventSlot(item->seq_clock, walk);
    if (item->seq_linear.operands.empty()) {
      WalkPackageSequenceReads(ctx, item);
    } else {
      ForEachBodySlot(item->seq_linear, walk);
    }
  });
}

// §26.2 holds for a class the package declares: its property initializers and
// its methods, those written in its body and the out-of-block bodies the
// package holds for it (§8.24), read its parameters and members as their own
// names, and a member access there reaches outside the package only through
// a design element's name (PackageRefContext::design_elements).
std::unordered_set<std::string_view> ClassMemberNames(const ClassDecl* cls) {
  std::unordered_set<std::string_view> members;
  for (const auto& [name, value] : cls->params) members.insert(name);
  for (const ClassMember* m : cls->members) {
    members.insert(m->kind == ClassMemberKind::kMethod ? m->method->name
                                                       : m->name);
  }
  return members;
}

void WalkClassBodies(PackageRefContext& ctx, const PackageDecl* pkg,
                     const ClassDecl* cls) {
  for (const ClassMember* m : cls->members) {
    if (m->init_expr != nullptr) WalkPackageRefExpr(ctx, m->init_expr);
    if (m->kind == ClassMemberKind::kMethod) WalkMethodBody(ctx, m->method);
  }
  for (const auto* body : pkg->items) {
    if (body->method_class == cls->name) WalkMethodBody(ctx, body);
  }
}

void WalkPackageClass(PackageRefContext& ctx, const PackageDecl* pkg,
                      const ModuleItem* item,
                      const std::unordered_set<std::string_view>& elements) {
  if (item->kind != ModuleItemKind::kClassDecl) return;
  const ClassDecl* cls = item->class_decl;
  ctx.design_elements = &elements;
  WalkWithNames(ctx, ClassMemberNames(cls),
                [&] { WalkClassBodies(ctx, pkg, cls); });
  ctx.design_elements = nullptr;
}

// The names of the design elements the unit declares, which a hierarchical
// reference from a package's class starts from (§23.6).
std::unordered_set<std::string_view> DesignElementNames(
    const CompilationUnit* unit) {
  std::unordered_set<std::string_view> names;
  for (const auto* scopes :
       {&unit->modules, &unit->interfaces, &unit->programs, &unit->checkers}) {
    for (const ModuleDecl* decl : *scopes) names.insert(decl->name);
  }
  return names;
}

}  // namespace

void Elaborator::ValidatePackageReferences() {
  std::unordered_set<std::string_view> known_package_names;
  for (const auto* pkg : unit_->packages) known_package_names.insert(pkg->name);

  std::unordered_set<std::string_view> cu_top_names = CollectCuTopNames(unit_);
  const std::unordered_set<std::string_view> kDesignElements =
      DesignElementNames(unit_);

  for (const auto* pkg : unit_->packages) {
    PackageRefContext ctx;
    ctx.unit = unit_;
    ctx.known_package_names = &known_package_names;
    ctx.cu_top_names = &cu_top_names;
    ctx.provided_names = &pkg_provided_names_;
    ctx.diag = &diag_;
    CollectPackageLocalNames(pkg, ctx);

    for (ModuleItem* item : pkg->items) {
      WalkPackageItemInit(ctx, item);
      WalkPackageSubroutine(ctx, item);
      WalkPackageProperty(ctx, item);
      WalkPackageSequence(ctx, item);
      WalkPackageClass(ctx, pkg, item, kDesignElements);
    }
  }
}

namespace {

using PkgByName = std::unordered_map<std::string_view, const PackageDecl*>;

// §26.5/§26.6: the set of names a package brings in by import. An explicit
// `import pkg::name` contributes a "pkg::name" key to direct_imports; a
// wildcard `import pkg::*` contributes the source package name to
// wildcard_sources. Both export-validation steps consult this same set, so it
// is one entity passed together rather than two loose parameters.
struct PackageImportSet {
  std::unordered_set<std::string> direct_imports;
  std::unordered_set<std::string_view> wildcard_sources;
};

// §6.19.2 (Table 6-10): the constants a ranged member generates are its
// written name followed by an index written as a decimal number, sub0 through
// sub4 for `sub[5]`, so `name` is one of them only when what follows the
// written name is such a number: digits alone, and no leading zero but for the
// index 0 itself, which is how FoldEnumMembers in elaborator_enum_constants.cpp
// writes them. The index is answered, or nothing when `name` has no such
// suffix; more than eighteen digits is past every range and past int64_t.
std::optional<int64_t> GeneratedIndexOf(std::string_view written,
                                        std::string_view name) {
  if (name.size() <= written.size() || !name.starts_with(written)) {
    return std::nullopt;
  }
  std::string_view digits = name.substr(written.size());
  if (digits.size() > 18 || (digits.size() > 1 && digits[0] == '0')) {
    return std::nullopt;
  }
  int64_t index = 0;
  for (char c : digits) {
    if (c < '0' || c > '9') return std::nullopt;
    index = (index * 10) + (c - '0');
  }
  return index;
}

// §6.19.2 (Table 6-10): `name[N]` generates name0 through nameN-1, and
// `name[N:M]` nameN through nameM, incrementing or decrementing from N to M;
// the written name itself names no constant. The bounds are folded without a
// scope, as ComputeEnumRangeCount in elaborator_validate_types.cpp folds them,
// this validation running before the package's parameters are registered; a
// bound that does not fold admits every index, on the permissive side a
// wildcard import is taken on.
bool RangedMemberGenerates(const EnumMember& em, std::string_view name) {
  auto index = GeneratedIndexOf(em.name, name);
  if (!index) return false;
  auto n = ConstEvalInt(em.range_start);
  if (!n) return true;
  if (em.range_end == nullptr) return *index < *n;
  auto m = ConstEvalInt(em.range_end);
  if (!m) return true;
  return *n <= *m ? *index >= *n && *index <= *m : *index >= *m && *index <= *n;
}

// §6.19: an enumerated type declares its literals as named constants of the
// scope holding the enum -- two enumerations naming one literal cannot stand
// in the same scope -- so a literal of an enumeration written in `type`, as
// the type itself (Syntax 6-5) or as the type of a member of a structure or
// union of it (§7.2), is a declaration of the scope as the type's own name is.
// A ranged member of §6.19.2 declares the constants it generates and not the
// name it is written with, as the provided-name walk of
// elaborator_scope_rules_names.cpp holds it too; this check folds each bound
// on the spot, where that walk asks EnumMemberDeclaredNames.
bool TypeDeclaresEnumLiteral(const DataType& type, std::string_view name) {
  for (const auto& em : type.enum_members) {
    if (em.range_start == nullptr ? em.name == name
                                  : RangedMemberGenerates(em, name)) {
      return true;
    }
  }
  for (const auto& sm : type.struct_members) {
    if (sm.nested_type != nullptr &&
        TypeDeclaresEnumLiteral(*sm.nested_type, name))
      return true;
  }
  return false;
}

// §26.6: the candidates for import from a package are the declarations the
// package makes: each item by its name, a class by the class's name, and the
// literals of the enumerations its typedefs and data declarations write
// (§26.5's package p declares FALSE and TRUE as it declares BOOL). What the
// package imports is no declaration of its own.
bool PackageDeclaresName(const PackageDecl* src_pkg, std::string_view name) {
  for (const auto* it : src_pkg->items) {
    if (it->kind == ModuleItemKind::kImportDecl ||
        it->kind == ModuleItemKind::kExportDecl)
      continue;
    if (it->kind == ModuleItemKind::kClassDecl && it->class_decl &&
        it->class_decl->name == name)
      return true;
    if (!it->name.empty() && it->name == name) return true;
    if (TypeDeclaresEnumLiteral(it->typedef_type, name) ||
        TypeDeclaresEnumLiteral(it->data_type, name))
      return true;
  }
  return false;
}

bool PackageProvidesName(const PackageDecl* src_pkg, std::string_view name,
                         const PkgByName& pkg_by_name,
                         std::unordered_set<const PackageDecl*>& visited);

// §26.6: whether `pkg` actually imports `name` from package `src` -- either
// through an explicit `import src::name` or through a wildcard `import src::*`.
// A wildcard import cannot be reference-tracked at this stage, so it is treated
// as importing every candidate name (an over-approximation on the permissive
// side); an explicit import contributes only the one name it lists.
bool PackageActuallyImports(const PackageDecl* pkg, std::string_view src,
                            std::string_view name) {
  for (const auto* item : pkg->items) {
    if (item->kind != ModuleItemKind::kImportDecl) continue;
    const auto& imp = item->import_item;
    if (imp.package_name != src) continue;
    if (imp.is_wildcard) return true;
    if (imp.item_name == name) return true;
  }
  return false;
}

// Handles an `export *::*` re-export: it re-exports the declarations the source
// package actually imported, so the name is provided only if it was imported
// (explicitly under that very name, or through a wildcard import) from a source
// package that in turn provides it.
bool WildcardExportProvidesName(
    const PackageDecl* src_pkg, std::string_view name,
    const PkgByName& pkg_by_name,
    const std::unordered_set<const PackageDecl*>& visited) {
  for (const auto* imp : src_pkg->items) {
    if (imp->kind != ModuleItemKind::kImportDecl) continue;
    const auto& ii = imp->import_item;
    if (!ii.is_wildcard && ii.item_name != name) continue;
    auto sit = pkg_by_name.find(ii.package_name);
    if (sit == pkg_by_name.end()) continue;
    auto sub = visited;
    if (PackageProvidesName(sit->second, name, pkg_by_name, sub)) return true;
  }
  return false;
}

// Handles a named re-export (`export pkg::name` or `export pkg::*`): the name
// is provided if the named source package provides it. For the `export pkg::*`
// form, §26.6 re-exports only names actually imported from pkg, so a wildcard
// export contributes a name only when the exporting package imported it.
bool NamedExportProvidesName(
    const PackageDecl* exporting_pkg, const ImportItem& ex,
    std::string_view name, const PkgByName& pkg_by_name,
    const std::unordered_set<const PackageDecl*>& visited) {
  auto sit = pkg_by_name.find(ex.package_name);
  if (sit == pkg_by_name.end()) return false;
  if (ex.is_wildcard) {
    if (!PackageActuallyImports(exporting_pkg, ex.package_name, name))
      return false;
  } else if (ex.item_name != name) {
    return false;
  }
  auto sub = visited;
  return PackageProvidesName(sit->second, name, pkg_by_name, sub);
}

bool PackageProvidesName(const PackageDecl* src_pkg, std::string_view name,
                         const PkgByName& pkg_by_name,
                         std::unordered_set<const PackageDecl*>& visited) {
  if (!visited.insert(src_pkg).second) return false;
  if (PackageDeclaresName(src_pkg, name)) return true;
  for (const auto* it : src_pkg->items) {
    if (it->kind != ModuleItemKind::kExportDecl) continue;
    const auto& ex = it->import_item;
    if (ex.package_name == "*") {
      if (WildcardExportProvidesName(src_pkg, name, pkg_by_name, visited))
        return true;
    } else if (NamedExportProvidesName(src_pkg, ex, name, pkg_by_name,
                                       visited)) {
      return true;
    }
  }
  return false;
}

void CollectPackageImports(const PackageDecl* pkg, PackageImportSet& imports) {
  for (const auto* item : pkg->items) {
    if (item->kind != ModuleItemKind::kImportDecl) continue;
    const auto& imp = item->import_item;
    if (imp.is_wildcard) {
      imports.wildcard_sources.insert(imp.package_name);
    } else {
      imports.direct_imports.insert(std::string(imp.package_name) +
                                    "::" + std::string(imp.item_name));
    }
  }
}

// Resolves the source package of a named export and confirms the source
// package actually provides the exported name. Returns the resolved source
// package, or nullptr after emitting the appropriate diagnostic.
const PackageDecl* ResolveExportSource(const ModuleItem* item,
                                       const ImportItem& ex,
                                       const PkgByName& pkg_by_name,
                                       DiagEngine& diag) {
  auto src_it = pkg_by_name.find(ex.package_name);
  if (src_it == pkg_by_name.end()) {
    diag.Error(item->loc,
               std::format("export from unknown package '{}'", ex.package_name),
               Subclause("26.6"));
    return nullptr;
  }
  std::unordered_set<const PackageDecl*> visited;
  if (!PackageProvidesName(src_it->second, ex.item_name, pkg_by_name,
                           visited)) {
    diag.Error(
        item->loc,
        std::format("'{}' is not a candidate for import from package '{}'",
                    ex.item_name, ex.package_name),
        Subclause("26.6"));
    return nullptr;
  }
  return src_it->second;
}

// §26.6: an exported name must first be imported by the exporting package,
// either explicitly or through a wildcard import of the source package.
void CheckExportIsImported(const PackageDecl* pkg, const ModuleItem* item,
                           const ImportItem& ex,
                           const PackageImportSet& imports, DiagEngine& diag) {
  auto key = std::string(ex.package_name) + "::" + std::string(ex.item_name);
  if (imports.direct_imports.count(key) == 0 &&
      imports.wildcard_sources.count(ex.package_name) == 0) {
    diag.Error(
        item->loc,
        std::format("export '{}::{}': '{}' is not imported in package '{}'",
                    ex.package_name, ex.item_name, ex.item_name, pkg->name),
        Subclause("26.6"));
  }
}

void ValidateOnePackageExportItem(const PackageDecl* pkg,
                                  const ModuleItem* item,
                                  const PkgByName& pkg_by_name,
                                  const PackageImportSet& imports,
                                  DiagEngine& diag) {
  const auto& ex = item->import_item;

  if (ex.package_name == "*" || ex.is_wildcard) return;

  if (ResolveExportSource(item, ex, pkg_by_name, diag) == nullptr) return;

  CheckExportIsImported(pkg, item, ex, imports, diag);
}

// §26.6: exporting a name that the package brought in only through a wildcard
// import (`import pkg::*; export pkg::name;`) makes the export itself count as
// a reference to that name, importing it into the package following the same
// rules as a direct import. §26.5 then forbids declaring that name locally once
// it has been claimed through the wildcard import, so a declaration of the
// exported name that follows the export in the same package is an error -- the
// package p6 example of this subclause.
// An export naming a single item claims that name when the exporting package
// only sees the item through a wildcard import rather than a direct one.
void RecordWildcardSourcedExport(
    const ImportItem& ex, const PackageImportSet& imports,
    std::unordered_set<std::string_view>& wildcard_export_refs) {
  if (ex.package_name == "*" || ex.is_wildcard) return;
  auto key = std::string(ex.package_name) + "::" + std::string(ex.item_name);
  if (imports.wildcard_sources.count(ex.package_name) != 0 &&
      imports.direct_imports.count(key) == 0) {
    wildcard_export_refs.insert(ex.item_name);
  }
}

// Whether the package item `pi` declares `name`: an item by its own name, a
// class declaration by the class's, or an enumeration it writes by one of its
// literals.
bool PackageItemDeclaresName(const ModuleItem* pi, std::string_view name) {
  if (pi->name == name) return true;
  if (pi->kind == ModuleItemKind::kClassDecl && pi->class_decl &&
      pi->class_decl->name == name) {
    return true;
  }
  // §6.19: an enumeration's literals are declarations of the scope its type
  // is declared in, so a literal of the name is a later declaration of it.
  return TypeDeclaresEnumLiteral(pi->typedef_type, name) ||
         TypeDeclaresEnumLiteral(pi->data_type, name);
}

// A declaration that follows such an export and supplies one of the claimed
// names is the conflict §26.6 forbids.
void ReportDeclarationAfterWildcardExport(
    const PackageDecl* pkg, const ModuleItem* item,
    const std::unordered_set<std::string_view>& wildcard_export_refs,
    DiagEngine& diag) {
  for (std::string_view name : wildcard_export_refs) {
    if (PackageItemDeclaresName(item, name)) {
      diag.Error(
          item->loc,
          std::format("declaration of '{}' in package '{}' follows an export "
                      "that referenced it through a wildcard package import",
                      name, pkg->name),
          Subclause("26.6"));
    }
  }
}

void CheckExportReferenceConflicts(const PackageDecl* pkg,
                                   const PackageImportSet& imports,
                                   DiagEngine& diag) {
  // Names claimed by such a wildcard-sourced export. Populated while walking
  // the item list in source order so that only a declaration appearing after
  // the export is flagged, matching the ordering the p6 example relies on.
  std::unordered_set<std::string_view> wildcard_export_refs;
  for (const auto* item : pkg->items) {
    if (item->kind == ModuleItemKind::kExportDecl) {
      RecordWildcardSourcedExport(item->import_item, imports,
                                  wildcard_export_refs);
      continue;
    }
    ReportDeclarationAfterWildcardExport(pkg, item, wildcard_export_refs, diag);
  }
}

}  // namespace

void Elaborator::ValidatePackageExports() {
  PkgByName pkg_by_name;
  for (const auto* pkg : unit_->packages) {
    pkg_by_name[pkg->name] = pkg;
  }

  for (const auto* pkg : unit_->packages) {
    PackageImportSet imports;
    CollectPackageImports(pkg, imports);

    for (const auto* item : pkg->items) {
      if (item->kind != ModuleItemKind::kExportDecl) continue;
      ValidateOnePackageExportItem(pkg, item, pkg_by_name, imports, diag_);
    }

    CheckExportReferenceConflicts(pkg, imports, diag_);
  }
}

namespace {

bool IsModportLiteralExpr(const Expr* e) {
  if (!e) return false;
  switch (e->kind) {
    case ExprKind::kIntegerLiteral:
    case ExprKind::kRealLiteral:
    case ExprKind::kTimeLiteral:
    case ExprKind::kStringLiteral:
    case ExprKind::kUnbasedUnsizedLiteral:
      return true;
    default:
      return false;
  }
}

// §25.5: the set of names an interface declares, against which its modport
// items are checked. declared_names holds the interface's own ports plus every
// item declared in its body; clocking_names holds just the clocking blocks.
// constant_names holds the subset that name a constant per §11.2.1 (a
// parameter, a localparam, or a const variable), used by §25.5.4 to reject a
// constant port expression bound to an output or inout port. A modport item
// naming anything outside declared_names is rejected.
struct ModportNameScope {
  std::unordered_set<std::string_view> declared_names;
  std::unordered_set<std::string_view> clocking_names;
  std::unordered_set<std::string_view> constant_names;
};

// §25.5: a modport may only reference names that this interface itself
// declares. Collect every such name — the interface's own ports plus the
// signals, subprograms, and other items declared in its body — so a modport
// item naming anything outside this set can be rejected below.
// Record what one interface item contributes to the name scope a modport is
// resolved against. §11.2.1: a parameter/localparam, or a const variable, is a
// constant.
void AddModportItemName(const ModuleItem* item, ModportNameScope& scope) {
  if (item->name.empty()) return;
  if (item->kind == ModuleItemKind::kClockingBlock) {
    scope.clocking_names.insert(item->name);
  }
  if (item->kind == ModuleItemKind::kParamDecl ||
      (item->kind == ModuleItemKind::kVarDecl && item->data_type.is_const)) {
    scope.constant_names.insert(item->name);
  }
  scope.declared_names.insert(item->name);
}

void CollectModportDeclaredNames(const ModuleDecl* iface,
                                 ModportNameScope& scope) {
  for (const auto& port : iface->ports) {
    if (!port.name.empty()) scope.declared_names.insert(port.name);
  }
  // §11.2.1: parameters declared in the interface's parameter port list are
  // constants, so a modport expression that names one is a constant expression.
  for (const auto& [pname, pexpr] : iface->params) {
    if (!pname.empty()) scope.constant_names.insert(pname);
  }
  for (const auto* item : iface->items) AddModportItemName(item, scope);
}

// §25.5: a plain simple modport item (one written as a bare identifier,
// not a `.name(expr)` modport expression, and not an imported/exported
// subprogram or a clocking item) names an object that this interface
// shall already declare. Naming something declared only by an enclosing
// scope, or nowhere at all, would implicitly create a new port and is
// illegal. §25.5.4: the `.name(...)` named-port form (including the empty
// `.name()`) is exempt — its identifier is a fresh port name, so it need not
// name a declared interface item.
void CheckSimpleModportItemDeclared(
    const ModuleDecl* iface, const ModportDecl* mp, const ModportPort& port,
    const std::unordered_set<std::string_view>& declared_names,
    DiagEngine& diag) {
  if (!port.is_clocking && !port.is_import && !port.is_export &&
      !port.is_named_port && !declared_names.contains(port.name)) {
    diag.Error(mp->loc,
               std::format("modport '{}' references '{}', which interface '{}' "
                           "does not declare",
                           mp->name, port.name, iface->name),
               Subclause("25.5"));
  }
}

// §25.5.4 / §11.2.1: a modport port expression is a constant either when it is
// a literal or when it names one of the interface's constants (a parameter,
// localparam, or const variable). Such an expression cannot serve as the target
// of a write and so is not a legal output/inout port expression (§23.3.3).
bool IsModportConstExpr(
    const Expr* e, const std::unordered_set<std::string_view>& constant_names) {
  if (IsModportLiteralExpr(e)) return true;
  if (e && e->kind == ExprKind::kIdentifier &&
      constant_names.contains(e->text)) {
    return true;
  }
  return false;
}

void CheckModportConstExprDirection(
    const ModportDecl* mp, const ModportPort& port,
    const std::unordered_set<std::string_view>& constant_names,
    DiagEngine& diag) {
  if (IsModportConstExpr(port.expr, constant_names) &&
      (port.direction == Direction::kOutput ||
       port.direction == Direction::kInout)) {
    diag.Error(mp->loc,
               std::format("port-id '{}' in modport '{}' has a constant port "
                           "expression and cannot be declared as output or "
                           "inout",
                           port.name, mp->name),
               Subclause("25.5.4"));
  }
}

void CheckModportClockingDeclared(
    const ModuleDecl* iface, const ModportDecl* mp, const ModportPort& port,
    const std::unordered_set<std::string_view>& clocking_names,
    DiagEngine& diag) {
  if (port.is_clocking && !clocking_names.contains(port.name)) {
    diag.Error(mp->loc,
               std::format("clocking identifier '{}' in modport '{}' is not "
                           "declared in interface '{}'",
                           port.name, mp->name, iface->name),
               Subclause("25.5.5"));
  }
}

void ValidateOneModportPort(const ModuleDecl* iface, const ModportDecl* mp,
                            const ModportPort& port,
                            const ModportNameScope& scope, DiagEngine& diag) {
  CheckSimpleModportItemDeclared(iface, mp, port, scope.declared_names, diag);
  CheckModportConstExprDirection(mp, port, scope.constant_names, diag);
  CheckModportClockingDeclared(iface, mp, port, scope.clocking_names, diag);
  CheckModportImport(iface, mp, port, diag);
}

void ValidateOneModport(const ModuleDecl* iface, const ModportDecl* mp,
                        const ModportNameScope& scope, DiagEngine& diag) {
  std::unordered_set<std::string_view> port_names;
  for (const auto& port : mp->ports) {
    if (port.name.empty()) continue;
    if (!port_names.insert(port.name).second) {
      diag.Error(mp->loc,
                 std::format("duplicate port-id '{}' in modport '{}'",
                             port.name, mp->name),
                 Subclause("25.5.4"));
    }
    ValidateOneModportPort(iface, mp, port, scope, diag);
  }
}

// The modports of `decl`, where it is an interface, and of every interface
// declared inside it at any depth. §25.5 holds a nested interface declaration's
// modport to that interface's own declarations as it holds a top-level one's:
// §23.4 makes the enclosing scope's names visible inside the nested
// declaration, but they are not its declarations, so a modport naming one would
// create a port.
void ValidateModportsOf(const ModuleDecl* decl, DiagEngine& diag) {
  if (decl->decl_kind == ModuleDeclKind::kInterface) {
    ModportNameScope scope;
    CollectModportDeclaredNames(decl, scope);
    for (auto* mp : decl->modports) ValidateOneModport(decl, mp, scope, diag);
  }
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kNestedModuleDecl &&
        item->nested_module_decl != nullptr)
      ValidateModportsOf(item->nested_module_decl, diag);
  }
}

}  // namespace

void Elaborator::ValidateModports() {
  for (const auto* decls :
       {&unit_->modules, &unit_->interfaces, &unit_->programs}) {
    for (const auto* decl : *decls) ValidateModportsOf(decl, diag_);
  }
}

}  // namespace delta
