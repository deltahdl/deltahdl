#include "elaborator/let_actual_check.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <format>
#include <optional>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/aggregate_shape.h"
#include "elaborator/bit_stream_width.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_class_lookup.h"
#include "elaborator/elaborator_class_typedef_specialization.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_classes_internal.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/let_construct.h"
#include "elaborator/let_name_frames.h"
#include "elaborator/net_data_type.h"
#include "elaborator/queue_dim.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {
namespace {

// Whether `t` is a value an integral or a real type gives: an integer type, an
// enum, a real, or a structure or union, which ActualFitsFormal is asked of
// only packed or soft (Judge takes an unpacked one by assignment or bit-stream
// cast) and which §6.11.1 then makes integral.
bool IsIntegralOrRealLike(const DataType& t) {
  return t.kind == DataTypeKind::kStruct || t.kind == DataTypeKind::kUnion ||
         IsIntegralType(t.kind) || IsRealType(t.kind);
}

// §6.24.3: the built-in kinds of a bit-stream type, a string or an integral
// type.
bool IsBitStreamKind(DataTypeKind kind) {
  return kind == DataTypeKind::kString || IsIntegralType(kind);
}

bool IsBitStreamType(const DataType& t, const TypedefMap& typedefs);

// A member of an unpacked structure as IsBitStreamType asks of it: its inline
// aggregate or enum, its built-in kind, or the type its name resolves to. A
// name resolving to no type, a class's, is taken as one.
bool IsBitStreamMember(const StructMember& m, const TypedefMap& typedefs) {
  if (m.nested_type != nullptr)
    return IsBitStreamType(*m.nested_type, typedefs);
  if (m.type_kind != DataTypeKind::kNamed) return IsBitStreamKind(m.type_kind);
  const DataType* named = MemberNamedType(m, typedefs);
  const DataType* end =
      named != nullptr ? TypeAtChainEnd(*named, typedefs) : nullptr;
  return end == nullptr || IsBitStreamType(*end, typedefs);
}

// §6.24.3: whether `t` is a bit-stream type -- an integral, packed or string
// type, or an unpacked structure whose members all are -- which an explicit
// cast converts to or from a string (§6.16) or another bit-stream type. An
// unpacked array of one is too, so an array's element type is what this is
// asked of. The clause's list names no unpacked union, so none is one, nor a
// structure holding one.
bool IsBitStreamType(const DataType& t, const TypedefMap& typedefs) {
  if (t.kind != DataTypeKind::kStruct && t.kind != DataTypeKind::kUnion)
    return IsBitStreamKind(t.kind);
  if (t.is_packed || t.is_soft) return true;
  if (t.kind == DataTypeKind::kUnion) return false;
  return std::ranges::all_of(t.struct_members, [&](const StructMember& m) {
    return IsBitStreamMember(m, typedefs);
  });
}

// §6.22.4 as §11.12 asks it of an actual and its typed formal, both followed
// through their typedefs. A string is cast compatible with another bit-stream
// type (§6.16, §6.24.3) and with no real, chandle or event, for which no cast
// is defined (§6.22.5).
bool ActualFitsFormal(const DataType& actual, const DataType& formal,
                      const TypedefMap& typedefs) {
  if (actual.kind == DataTypeKind::kString)
    return IsBitStreamType(formal, typedefs);
  if (formal.kind == DataTypeKind::kString)
    return IsBitStreamType(actual, typedefs);
  return IsCastCompatible(actual, formal) ||
         (IsIntegralOrRealLike(actual) && IsIntegralOrRealLike(formal));
}

// The hops a chain of typedef names is followed through. A longer chain, as a
// cycle of names makes one, is left unjudged.
constexpr int kMaxTypedefHops = 32;

// One unpacked dimension of a side, with the frame the names its bounds are
// written with are looked up in.
struct SideDim {
  const Expr* dim;
  const NameFrame* scope;
};

// One side of a call, the variable an actual names or the formal it binds,
// its type followed through the declarations of the names on the way: the
// type the chain ends in, the class that is where the chain names one, and
// the unpacked dimensions, slowest varying first -- the declaration's own,
// then each typedef's in turn (§7.4.5).
struct ResolvedSide {
  const DataType* end = nullptr;
  const ClassDecl* cls = nullptr;
  std::vector<SideDim> dims;
};

// What a route to cast compatibility shows of one pair: that the actual fits,
// that it does not, or neither, where a size or a type is not known before the
// design runs.
enum class Verdict : std::uint8_t { kFits, kFails, kUnknown };

enum class DimKind : std::uint8_t { kFixed, kDynamic, kAssociative };

// An unpacked dimension's kind, and for a fixed-size one its element count
// where it folds.
struct DimShape {
  DimKind kind = DimKind::kFixed;
  std::optional<uint32_t> count;
};

// Fails where either fails, else is not known where either is not.
Verdict Both(Verdict a, Verdict b) {
  if (a == Verdict::kFails || b == Verdict::kFails) return Verdict::kFails;
  if (a == Verdict::kUnknown || b == Verdict::kUnknown)
    return Verdict::kUnknown;
  return Verdict::kFits;
}

Verdict FitsWhen(bool fits) { return fits ? Verdict::kFits : Verdict::kFails; }

// Whether `cls`, or a class it derives from, declares a local or protected
// member (§8.18), which an object of the class holds whether or not it is
// seen.
bool DeclaresHiddenMember(const ClassDecl* cls, const CompilationUnit* unit) {
  for (; cls != nullptr; cls = FindBaseClass(cls, unit)) {
    for (const ClassMember* m : cls->members) {
      if (m->is_local || m->is_protected) return true;
    }
  }
  return false;
}

bool IsBlockLet(const Stmt* s) {
  return s->kind == StmtKind::kBlockItemDecl &&
         s->decl_item->kind == ModuleItemKind::kLetDecl;
}

void AddDims(ResolvedSide& side, const std::vector<Expr*>* dims,
             const NameFrame* scope) {
  if (dims == nullptr) return;
  for (const Expr* dim : *dims) side.dims.push_back({dim, scope});
}

// §7.6: the slowest-varying dimensions of an actual and a formal under
// assignment. An associative array takes only another (§7.9.9), whose index
// types this does not compare; a dynamic or queue formal takes any number of
// elements; a fixed-size formal takes as many as it has.
Verdict SlowestDimensionsAssign(const DimShape& actual,
                                const DimShape& formal) {
  if (actual.kind == DimKind::kAssociative ||
      formal.kind == DimKind::kAssociative)
    return actual.kind == formal.kind ? Verdict::kUnknown : Verdict::kFails;
  if (formal.kind != DimKind::kFixed) return Verdict::kFits;
  if (actual.kind != DimKind::kFixed || !actual.count || !formal.count)
    return Verdict::kUnknown;
  return FitsWhen(*actual.count == *formal.count);
}

// §7.6 with §6.22.2: a faster-varying dimension of the two is equivalent, of
// one fixed size.
Verdict FasterDimensionsMatch(const DimShape& actual, const DimShape& formal) {
  if (actual.kind != DimKind::kFixed || formal.kind != DimKind::kFixed ||
      !actual.count || !formal.count)
    return Verdict::kUnknown;
  return FitsWhen(*actual.count == *formal.count);
}

// A formal, with the type it takes (LetFormalTypes) and the frame of the
// scope declaring its let.
struct BoundFormal {
  const FunctionArg& arg;
  const DataType* type;
  const NameFrame& scope;
};

// The walk of one scope's items for the calls of lets they write, each judged
// by §11.12's rule 2. `unit` is the compilation unit's frame, which `$unit::`
// names, and `parameter_frame` the frame whose parameters the context's
// parameter values are: a dimension folds only from names it declares.
class LetActualWalk {
 public:
  LetActualWalk(const LetActualContext& ctx, const PackageFrames& packages,
                ClassFrames& classes, const NameFrame& unit,
                const NameFrame& parameter_frame)
      : ctx_(ctx),
        packages_(packages),
        classes_(classes),
        unit_(unit),
        parameter_frame_(parameter_frame) {}

  void CheckItems(const std::vector<ModuleItem*>& items,
                  const NameFrame& frame) const {
    for (const ModuleItem* item : items) CheckItem(item, frame);
  }

  // The implicit nets the items of the scope of `frame` declare (§6.10),
  // where the design element assumes any.
  void DeclareImplicit(NameFrame& frame,
                       const std::vector<ModuleItem*>& items) const {
    if (ctx_.implicit_nets) DeclareImplicitNets(frame, items);
  }

 private:
  void CheckItem(const ModuleItem* item, const NameFrame& frame) const {
    switch (item->kind) {
      case ModuleItemKind::kGenerateIf:
      case ModuleItemKind::kGenerateFor:
      case ModuleItemKind::kGenerateCase:
        CheckGenerate(item, frame);
        return;
      case ModuleItemKind::kLetDecl:
        CheckLet(item, frame);
        return;
      case ModuleItemKind::kFunctionDecl:
      case ModuleItemKind::kTaskDecl:
        CheckSubroutine(item, frame);
        return;
      default:
        break;
    }
    CheckExpr(item->assign_lhs, frame);
    CheckExpr(item->assign_rhs, frame);
    CheckExpr(item->init_expr, frame);
    CheckStmt(item->body, frame);
    CheckBody(item->func_body_stmts, frame);
  }

  // §27.3: each generate block is a scope of its own within the one around
  // it, and a loop's block declares its genvar as a localparam (§27.4).
  void CheckGenerate(const ModuleItem* item, const NameFrame& frame) const {
    if (item->kind == ModuleItemKind::kGenerateCase) {
      for (const GenerateCaseItem& choice : item->gen_case_items)
        CheckGenerateBlock(choice.body, frame, {});
      return;
    }
    const bool kLoop = item->kind == ModuleItemKind::kGenerateFor;
    CheckGenerateBlock(item->gen_body, frame,
                       kLoop ? item->gen_init->var_name : std::string_view{});
    if (item->gen_else != nullptr) CheckGenerate(item->gen_else, frame);
  }

  void CheckGenerateBlock(const std::vector<ModuleItem*>& items,
                          const NameFrame& frame,
                          std::string_view genvar) const {
    NameFrame block(&frame);
    DeclareOther(block, genvar);
    DeclareScope(block, items, packages_);
    DeclareImplicit(block, items);
    CheckItems(items, block);
  }

  // A subroutine's formals and its own name, its result's variable (§13.4.1),
  // are its body's. An out-of-block body is its class's method (§8.24), whose
  // properties this walk does not hold, so it is left alone.
  void CheckSubroutine(const ModuleItem* item, const NameFrame& frame) const {
    if (!item->method_class.empty()) return;
    NameFrame formals(&frame);
    DeclareOther(formals, item->name);
    for (const FunctionArg& arg : item->func_args)
      DeclareOther(formals, arg.name);
    CheckBody(item->func_body_stmts, formals);
  }

  void CheckBody(const std::vector<Stmt*>& stmts,
                 const NameFrame& frame) const {
    std::vector<Stmt*> present = stmts;
    std::erase(present, nullptr);
    if (present.empty()) return;
    NameFrame body(&frame);
    DeclareStatements(body, present, packages_);
    for (const Stmt* s : present) CheckStmt(s, body);
  }

  // A let's defaults are its declaration's (§11.12), judged where it is
  // declared, and its body sees its formals.
  void CheckLet(const ModuleItem* let, const NameFrame& frame) const {
    const std::vector<const DataType*> kTypes = LetFormalTypes(let->func_args);
    for (size_t i = 0; i < kTypes.size(); ++i) {
      const FunctionArg& formal = let->func_args[i];
      CheckActual(formal.default_value, {formal, kTypes[i], frame}, frame);
    }
    NameFrame body(&frame);
    for (const FunctionArg& arg : let->func_args) DeclareOther(body, arg.name);
    CheckExpr(let->init_expr, body);
  }

  // A begin-end keeps its declarations among its statements and a fork among
  // its fork statements (Parser::ParseBlockVarDecls), each seen by every
  // statement the block holds, and a for or a foreach loop declares its
  // variables for its own header and body.
  void CheckStmt(const Stmt* s, const NameFrame& frame) const {
    if (s == nullptr) return;
    if (IsBlockLet(s)) {
      CheckLet(s->decl_item, frame);
      return;
    }
    NameFrame own(&frame);
    DeclareStatementScope(own, s, packages_);
    ForEachChildExpr(s, [&](Expr* const& e) { CheckExpr(e, own); });
    ForEachChildStmt(s, [&](Stmt* const& sub) { CheckStmt(sub, own); });
  }

  void CheckExpr(const Expr* e, const NameFrame& frame) const {
    auto check = [this, &frame](const Expr* under) { CheckCall(under, frame); };
    ForEachExprUnder(e, check);
  }

  void CheckCall(const Expr* e, const NameFrame& frame) const {
    if (e->kind != ExprKind::kCall || e->lhs == nullptr) return;
    const NameBinding* callee = Callee(*e->lhs, frame);
    if (callee == nullptr || callee->kind != NameKind::kLet) return;
    const auto& formals = callee->item->func_args;
    const std::vector<const DataType*> kTypes = LetFormalTypes(formals);
    const size_t kPositional = e->args.size() - e->arg_names.size();
    for (size_t i = 0; i < formals.size(); ++i) {
      const int kAt = ResolveActualArgIndex(e, i, formals[i].name, kPositional);
      if (kAt >= 0)
        CheckActual(e->args[static_cast<size_t>(kAt)],
                    {formals[i], kTypes[i], *callee->scope}, frame);
    }
  }

  // What a call's name reaches: `p::f` the `f` the package `p` declares, where
  // no class or typedef the scope sees is named `p` (§8.23); `$unit::f` the
  // compilation unit's own (§3.12.1); a bare name what the scopes around the
  // call bind it to. A hierarchical name reaches none (§11.12).
  const NameBinding* Callee(const Expr& callee, const NameFrame& frame) const {
    if (callee.kind == ExprKind::kIdentifier) return Named(callee, frame);
    if (callee.kind != ExprKind::kMemberAccess || !callee.is_scope_resolution ||
        callee.lhs->kind != ExprKind::kIdentifier)
      return nullptr;
    const NameBinding* prefix = FindName(frame, callee.lhs->text);
    if (prefix != nullptr && (prefix->kind == NameKind::kClass ||
                              prefix->kind == NameKind::kTypedef))
      return nullptr;
    return FindOwnName(packages_.Find(callee.lhs->text), callee.rhs->text);
  }

  // What an identifier, bare or behind `$unit::`, names at `frame`.
  const NameBinding* Named(const Expr& id, const NameFrame& frame) const {
    if (id.scope_prefix == "$unit") return FindOwnName(&unit_, id.text);
    if (!id.scope_prefix.empty()) return nullptr;
    return FindName(frame, id.text);
  }

  // §11.12, rule 2: an actual naming a variable is judged by the variable's
  // declared type against the type its formal takes (LetFormalTypes), each
  // read in the scope declaring it. An untyped formal, whose type is null,
  // takes any actual, and an event formal's actual is an event expression.
  void CheckActual(const Expr* actual, const BoundFormal& formal,
                   const NameFrame& call_scope) const {
    if (formal.type == nullptr || formal.type->kind == DataTypeKind::kEvent ||
        actual == nullptr || actual->kind != ExprKind::kIdentifier)
      return;
    const NameBinding* variable = Named(*actual, call_scope);
    if (variable == nullptr || variable->kind != NameKind::kVariable) return;
    const std::optional<ResolvedSide> kActual =
        Resolve(*variable->type, variable->dims, *variable->scope);
    const std::optional<ResolvedSide> kFormal =
        Resolve(*formal.type, &formal.arg.unpacked_dims, formal.scope);
    if (!kActual || !kFormal || Judge(*kActual, *kFormal) != Verdict::kFails)
      return;
    ctx_.diag.Error(
        actual->range.start,
        std::format("let actual argument '{}' is not cast compatible with the "
                    "type of formal '{}'",
                    actual->text, formal.arg.name),
        Subclause("11.12"));
  }

  // `type`, declared with the unpacked dimensions `dims` in the scope of
  // `scope`, followed through each typedef name to the type the chain ends
  // in, each name looked up in the scope declaring the typedef before it.
  // Nothing where a name is not known or a type reference is not resolved.
  std::optional<ResolvedSide> Resolve(const DataType& type,
                                      const std::vector<Expr*>* dims,
                                      const NameFrame& scope) const {
    ResolvedSide side;
    AddDims(side, dims, &scope);
    const DataType* at = &type;
    const NameFrame* in = &scope;
    for (int hop = 0; hop < kMaxTypedefHops; ++hop) {
      if (at->type_ref_expr != nullptr) return std::nullopt;
      if (at->kind != DataTypeKind::kNamed) {
        side.end = at;
        return side;
      }
      const NameBinding* named = TypeName(*at, *in);
      if (named == nullptr || named->kind == NameKind::kClass)
        return EndInClassOrSpecialization(std::move(side), *at, *in, named);
      if (named->kind != NameKind::kTypedef ||
          !named->item->typedef_ifc_port.empty())
        return std::nullopt;
      AddDims(side, &named->item->unpacked_dims, named->scope);
      at = &named->item->typedef_type;
      in = named->scope;
    }
    return std::nullopt;
  }

  // The declaration a type's name reaches: a bare name through the scopes
  // around `scope`, and a name behind prefixes the one the scope they name
  // declares (ScopeNamed). None where the prefixes name no scope with a
  // frame, which leaves a class's name to ClassOfDeclaredType.
  const NameBinding* TypeName(const DataType& type,
                              const NameFrame& scope) const {
    if (type.scope_name.empty()) return FindName(scope, type.type_name);
    return FindOwnName(ScopeNamed(type, scope), type.type_name);
  }

  // The frame of the scope a type's prefixes name, outermost first: `$unit`
  // the compilation unit's (§3.12.1), a class the scopes around `scope` see
  // under the first prefix (§8.23), else the package of that name (§26.3),
  // and each later prefix a class the scope before it declares, so that
  // `C::t`, `p::C::t` and `Outer::Inner::t` each reach the typedef the class
  // declares. Null where a prefix names none, or a class with no frame
  // (ClassFrames).
  const NameFrame* ScopeNamed(const DataType& type,
                              const NameFrame& scope) const {
    std::vector<std::string_view> prefixes = type.outer_scope_names;
    prefixes.push_back(type.scope_name);
    const NameFrame* frame = OutermostScope(prefixes.front(), scope);
    for (size_t i = 1; frame != nullptr && i < prefixes.size(); ++i)
      frame = ClassFrame(FindOwnName(frame, prefixes[i]));
    return frame;
  }

  const NameFrame* OutermostScope(std::string_view prefix,
                                  const NameFrame& scope) const {
    if (prefix == "$unit") return &unit_;
    const NameBinding* named = FindName(scope, prefix);
    if (named == nullptr || named->kind != NameKind::kClass)
      return packages_.Find(prefix);
    return classes_.Of(*named->cls, *named->scope);
  }

  // The frame of the class `named` declares, null where it is no class's.
  const NameFrame* ClassFrame(const NameBinding* named) const {
    if (named == nullptr || named->kind != NameKind::kClass) return nullptr;
    return classes_.Of(*named->cls, *named->scope);
  }

  // A chain whose name `type`, written in the scope of `scope`, reaches no
  // typedef: a specialization's (EndInSpecialization) where it reaches none
  // at all, else a class's (EndInClass).
  std::optional<ResolvedSide> EndInClassOrSpecialization(
      ResolvedSide side, const DataType& type, const NameFrame& scope,
      const NameBinding* named) const {
    if (named == nullptr) {
      const std::optional<SpecializedClassType> kSpecialized =
          SpecializeClassScopedType(type, ctx_.unit, ctx_.parameters,
                                    ctx_.shapes.typedefs, ctx_.arena);
      if (kSpecialized)
        return EndInSpecialization(std::move(side), *kSpecialized, scope);
    }
    return EndInClass(std::move(side), type, named);
  }

  // §8.25.1: a type behind a class with parameters, `P#()::t` or `P#(4)::t`,
  // which no frame of the class follows, is the typedef of that
  // specialization, with its dimensions and the specialization's values
  // folded in (SpecializeClassScopedType). Nothing where the specialized type
  // is still a name: written in the class, it has no frame to be followed in.
  std::optional<ResolvedSide> EndInSpecialization(
      ResolvedSide side, const SpecializedClassType& specialized,
      const NameFrame& scope) const {
    if (specialized.type.kind == DataTypeKind::kNamed) return std::nullopt;
    AddDims(side, &specialized.unpacked_dims, &scope);
    side.end = ctx_.arena.Create<DataType>(specialized.type);
    return side;
  }

  // A chain ending in `type`, the name of a class: the class `named` declares,
  // or else the one ClassOfDeclaredType finds by the name as written, a class
  // nested in a class or a package's (§8.23, §26.3). Nothing where neither is
  // one.
  std::optional<ResolvedSide> EndInClass(ResolvedSide side,
                                         const DataType& type,
                                         const NameBinding* named) const {
    side.cls = named != nullptr ? named->cls
                                : ClassOfDeclaredType(type, {}, ctx_.unit);
    if (side.cls == nullptr) return std::nullopt;
    side.end = &type;
    return side;
  }

  // §6.22.4: an actual fits where it is assignment compatible with the formal
  // or an explicit cast is defined between them. Classes go by their
  // hierarchy; two other types neither of them an unpacked array, structure or
  // union by ActualFitsFormal; and any other pair by assignment (§7.6) or by a
  // bit-stream cast (§6.24.3).
  Verdict Judge(const ResolvedSide& actual, const ResolvedSide& formal) const {
    if (actual.cls != nullptr || formal.cls != nullptr)
      return ClassesFit(actual, formal);
    const bool kAggregate = !actual.dims.empty() || !formal.dims.empty() ||
                            IsUnpackedAggregate(actual.end) ||
                            IsUnpackedAggregate(formal.end);
    if (!kAggregate)
      return FitsWhen(
          ActualFitsFormal(*actual.end, *formal.end, ctx_.shapes.typedefs));
    const Verdict kAssigned = AssignmentRoute(actual, formal);
    return kAssigned == Verdict::kFails ? BitStreamRoute(actual, formal)
                                        : kAssigned;
  }

  // §6.24.3 makes a class illegal as a bit-stream cast's destination, so a
  // formal holding class handles takes an actual by assignment alone: a lone
  // handle by its hierarchy -- §8.12 passes one up it and §8.16 down it by
  // $cast, so two classes fit where they are one or one derives from the
  // other (IsClassDeclDerivedFrom, which follows interface classes too) --
  // and an array by §7.6, its elements of the formal's own class, which
  // §6.22.2 makes equivalent to itself alone. Handles for a formal holding
  // none are HandlesAsBitStream's.
  Verdict ClassesFit(const ResolvedSide& actual,
                     const ResolvedSide& formal) const {
    if (formal.cls == nullptr) return HandlesAsBitStream(actual, formal);
    if (actual.cls == nullptr) return Verdict::kFails;
    if (actual.dims.empty() && formal.dims.empty())
      return FitsWhen(
          actual.cls == formal.cls ||
          IsClassDeclDerivedFrom(actual.cls, formal.cls->name, ctx_.unit) ||
          IsClassDeclDerivedFrom(formal.cls, actual.cls->name, ctx_.unit));
    if (actual.cls != formal.cls) return Verdict::kFails;
    return DimensionsAssign(actual, formal);
  }

  // §6.24.3: class handles convert by a bit-stream cast to a bit-stream type
  // other than an associative array, unless their class, or one it derives
  // from, declares a local or protected member. A non-null handle gives the
  // members of the object it refers to, which may be of a class derived from
  // its own, and a null one gives nothing (§11.4.14.1), so how many bits
  // handles give is not known before the design runs. §6.22.5 has a handle
  // type incompatible with every type but a class's; were that to decide
  // here, §6.24.3's rule on a source's local and protected members would
  // have nothing to apply to.
  Verdict HandlesAsBitStream(const ResolvedSide& actual,
                             const ResolvedSide& formal) const {
    const bool kAssociative =
        !formal.dims.empty() &&
        Shape(formal.dims.front()).kind == DimKind::kAssociative;
    if (kAssociative || !IsBitStreamType(*formal.end, ctx_.shapes.typedefs) ||
        DeclaresHiddenMember(actual.cls, ctx_.unit))
      return Verdict::kFails;
    return Verdict::kUnknown;
  }

  // §7.6: an unpacked array is assignment compatible with another of as many
  // unpacked dimensions whose element types are equivalent (§6.22.2), the
  // faster-varying dimensions included, and, where the formal is fixed size,
  // of as many elements. An unpacked structure or union is with a type
  // equivalent to it alone, which no integral or real rule widens.
  Verdict AssignmentRoute(const ResolvedSide& actual,
                          const ResolvedSide& formal) const {
    if (!TypesEquivalent(*actual.end, *formal.end)) return Verdict::kFails;
    return DimensionsAssign(actual, formal);
  }

  // §7.6: the unpacked dimensions of two sides whose element types are
  // equivalent assign where they are as many, each faster-varying one of the
  // other's size, and the slowest as SlowestDimensionsAssign has it.
  Verdict DimensionsAssign(const ResolvedSide& actual,
                           const ResolvedSide& formal) const {
    if (actual.dims.size() != formal.dims.size()) return Verdict::kFails;
    if (actual.dims.empty()) return Verdict::kFits;
    Verdict verdict = SlowestDimensionsAssign(Shape(actual.dims.front()),
                                              Shape(formal.dims.front()));
    for (size_t i = 1; i < actual.dims.size(); ++i)
      verdict = Both(verdict, FasterDimensionsMatch(Shape(actual.dims[i]),
                                                    Shape(formal.dims[i])));
    return verdict;
  }

  // §6.24.3: a bit-stream cast converts between two bit-stream types, never to
  // an associative array, and between two fixed-size ones only of one size.
  Verdict BitStreamRoute(const ResolvedSide& actual,
                         const ResolvedSide& formal) const {
    if (!formal.dims.empty() &&
        Shape(formal.dims.front()).kind == DimKind::kAssociative)
      return Verdict::kFails;
    const TypedefMap& typedefs = ctx_.shapes.typedefs;
    if (!IsBitStreamType(*actual.end, typedefs) ||
        !IsBitStreamType(*formal.end, typedefs))
      return Verdict::kFails;
    const std::optional<uint64_t> kActualBits = BitSize(actual);
    const std::optional<uint64_t> kFormalBits = BitSize(formal);
    if (!kActualBits || !kFormalBits) return Verdict::kUnknown;
    return FitsWhen(*kActualBits == *kFormalBits);
  }

  // The number of bits a fixed-size side holds; nothing for a side of a
  // dynamically sized type, a string being a dynamic array of bytes to a
  // bit-stream cast (§6.24.3), or of a size not known here.
  std::optional<uint64_t> BitSize(const ResolvedSide& side) const {
    if (side.end->kind == DataTypeKind::kString) return std::nullopt;
    const uint32_t kWidth = BitStreamTypeWidth(*side.end, ctx_.shapes.typedefs);
    if (kWidth == 0) return std::nullopt;
    uint64_t bits = kWidth;
    for (const SideDim& dim : side.dims) {
      const DimShape kShape = Shape(dim);
      if (kShape.kind != DimKind::kFixed || !kShape.count) return std::nullopt;
      bits *= *kShape.count;
    }
    return bits;
  }

  DimShape Shape(const SideDim& dim) const {
    if (dim.dim == nullptr || IsQueueDim(dim.dim))
      return {DimKind::kDynamic, std::nullopt};
    if (!IsFixedSizeUnpackedDim(dim.dim, ctx_.shapes))
      return {DimKind::kAssociative, std::nullopt};
    return {DimKind::kFixed, FoldedCount(dim)};
  }

  // A fixed-size dimension's element count, folded from the context's
  // parameter values where every name its bounds are written with is one the
  // parameter frame declares, so that no name of a scope within it or around
  // it is read as the parameter of the same name.
  std::optional<uint32_t> FoldedCount(const SideDim& dim) const {
    bool folds = true;
    auto check = [&](const Expr* e) {
      if (e->kind != ExprKind::kIdentifier) return;
      const NameBinding* named =
          e->scope_prefix.empty() ? FindName(*dim.scope, e->text) : nullptr;
      if (named == nullptr || named->scope != &parameter_frame_) folds = false;
    };
    ForEachExprUnder(dim.dim, check);
    if (!folds) return std::nullopt;
    return FixedDimElementCount(dim.dim, ctx_.parameters);
  }

  const LetActualContext& ctx_;
  const PackageFrames& packages_;
  ClassFrames& classes_;
  const NameFrame& unit_;
  const NameFrame& parameter_frame_;
};

}  // namespace

void CheckLetActualsOfDesignElement(const ModuleDecl& decl,
                                    const std::vector<ModuleItem*>& unit_items,
                                    const LetActualContext& ctx) {
  const PackageFrames kPackages(ctx.unit);
  NameFrame unit(nullptr);
  DeclareUnitScope(unit, unit_items, *ctx.unit, kPackages);
  NameFrame element(&unit);
  DeclareHeader(element, decl);
  DeclareScope(element, decl.items, kPackages);
  ClassFrames classes(kPackages);
  const LetActualWalk kWalk(ctx, kPackages, classes, unit, element);
  kWalk.DeclareImplicit(element, decl.items);
  kWalk.CheckItems(decl.items, element);
}

void CheckLetActualsOfUnitAndPackages(const LetActualContext& ctx) {
  const PackageFrames kPackages(ctx.unit);
  NameFrame unit(nullptr);
  DeclareUnitScope(unit, ctx.unit->cu_items, *ctx.unit, kPackages);
  ClassFrames classes(kPackages);
  const LetActualWalk kUnitWalk(ctx, kPackages, classes, unit, unit);
  kUnitWalk.CheckItems(ctx.unit->cu_items, unit);
  // A package's parameters are held under keys of their package's, not under
  // the bare names its dimensions are written with, so a package's
  // dimensions fold from literals alone.
  const ScopeMap kNoParameters;
  const LetActualContext kPackageCtx{ctx.unit, ctx.shapes, kNoParameters,
                                     ctx.diag, ctx.arena,  false};
  for (const auto& [pkg, frame] : kPackages.All()) {
    const LetActualWalk kWalk(kPackageCtx, kPackages, classes, unit, *frame);
    kWalk.CheckItems(pkg->items, *frame);
  }
}

}  // namespace delta
