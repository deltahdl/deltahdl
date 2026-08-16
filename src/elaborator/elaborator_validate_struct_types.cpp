#include <algorithm>
#include <cmath>
#include <format>
#include <optional>
#include <unordered_map>
#include <unordered_set>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

static uint32_t InferTypeRefExprWidth(const Expr* expr,
                                      const RtlirModule* mod) {
  if (!expr) return 0;
  switch (expr->kind) {
    case ExprKind::kIdentifier:
      for (const auto& v : mod->variables) {
        if (v.name == expr->text) return v.width;
      }
      for (const auto& n : mod->nets) {
        if (n.name == expr->text) return n.width;
      }
      return 0;
    case ExprKind::kIntegerLiteral:
      return ExtractLiteralWidth(expr->text);
    case ExprKind::kBinary: {
      uint32_t lw = InferTypeRefExprWidth(expr->lhs, mod);
      uint32_t rw = InferTypeRefExprWidth(expr->rhs, mod);
      return std::max(lw, rw);
    }
    case ExprKind::kTernary: {
      uint32_t tw = InferTypeRefExprWidth(expr->true_expr, mod);
      uint32_t fw = InferTypeRefExprWidth(expr->false_expr, mod);
      return std::max(tw, fw);
    }
    case ExprKind::kConcatenation: {
      uint32_t total = 0;
      for (const auto* el : expr->elements) {
        total += InferTypeRefExprWidth(el, mod);
      }
      return total;
    }
    case ExprKind::kUnary:
      return InferTypeRefExprWidth(expr->lhs, mod);
    default:
      return 0;
  }
}

static bool InferTypeRefExprSigned(const Expr* expr, const RtlirModule* mod) {
  if (!expr) return false;
  switch (expr->kind) {
    case ExprKind::kIdentifier:
      for (const auto& v : mod->variables) {
        if (v.name == expr->text) return v.is_signed;
      }
      for (const auto& n : mod->nets) {
        if (n.name == expr->text) return n.is_signed;
      }
      return false;
    case ExprKind::kBinary:
      return InferTypeRefExprSigned(expr->lhs, mod) &&
             InferTypeRefExprSigned(expr->rhs, mod);
    case ExprKind::kTernary:
      return InferTypeRefExprSigned(expr->true_expr, mod) &&
             InferTypeRefExprSigned(expr->false_expr, mod);
    case ExprKind::kConcatenation:
      return false;
    case ExprKind::kUnary:
      return InferTypeRefExprSigned(expr->lhs, mod);
    default:
      return false;
  }
}

// §6.23: build the packed dimension [width-1:0] of a type_reference resolved to
// a known scalar/vector width (no dimension is added for a 1-bit scalar).
static void SetTypeRefPackedDims(DataType& dt, uint32_t width, Arena& arena) {
  if (width <= 1) return;
  auto* left = arena.Create<Expr>();
  left->kind = ExprKind::kIntegerLiteral;
  left->int_val = static_cast<int64_t>(width - 1);
  auto* right = arena.Create<Expr>();
  right->kind = ExprKind::kIntegerLiteral;
  right->int_val = 0;
  dt.packed_dim_left = left;
  dt.packed_dim_right = right;
}

// §8.23 names the type operator as a context in which a class scope resolution
// may prefix a type name, so `type(Frame::payload_t)` denotes the typedef
// `payload_t` declared in class `Frame`. `Frame::payload_t` parses to a
// kMemberAccess node, which ResolveTypeRef would otherwise treat as an
// expression whose width and signedness are unknown, making the declared object
// a 1-bit unsigned logic instead of the type the typedef names. Returns false,
// leaving `dt` untouched, when `ref` is not a class scope resolution over two
// identifiers or when the class or its typedef is not visible.
static bool ResolveClassScopedTypeRef(DataType& dt, const Expr* ref,
                                      const CompilationUnit* unit) {
  if (ref->kind != ExprKind::kMemberAccess || !ref->is_scope_resolution) {
    return false;
  }
  if (ref->lhs == nullptr || ref->lhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  if (ref->rhs == nullptr || ref->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  const DataType* resolved =
      FindClassScopedTypedefType(ref->lhs->text, ref->rhs->text, unit);
  if (resolved == nullptr) return false;
  dt.kind = resolved->kind;
  dt.is_signed = resolved->is_signed;
  dt.type_name = resolved->type_name;
  dt.packed_dim_left = resolved->packed_dim_left;
  dt.packed_dim_right = resolved->packed_dim_right;
  dt.extra_packed_dims = resolved->extra_packed_dims;
  dt.type_ref_expr = nullptr;
  return true;
}

void Elaborator::ResolveTypeRef(ModuleItem* item, const RtlirModule* mod) {
  if (!item->data_type.type_ref_expr) return;
  auto* ref = item->data_type.type_ref_expr;
  CheckTypeRefArgInner(ref, item->loc);
  if (ResolveClassScopedTypeRef(item->data_type, ref, unit_)) return;
  if (ref->kind != ExprKind::kIdentifier) {
    item->data_type.kind = DataTypeKind::kLogic;
    SetTypeRefPackedDims(item->data_type, InferTypeRefExprWidth(ref, mod),
                         arena_);
    item->data_type.is_signed = InferTypeRefExprSigned(ref, mod);
    item->data_type.type_ref_expr = nullptr;
    return;
  }
  for (const auto& v : mod->variables) {
    if (v.name != ref->text) continue;
    item->data_type.kind = var_types_[ref->text];
    item->data_type.is_signed = v.is_signed;
    if (item->data_type.kind == DataTypeKind::kLogic ||
        item->data_type.kind == DataTypeKind::kBit ||
        item->data_type.kind == DataTypeKind::kReg) {
      SetTypeRefPackedDims(item->data_type, v.width, arena_);
    }
    item->data_type.type_ref_expr = nullptr;
    return;
  }
  // §6.23: type(net) yields the net's underlying data type (a logic vector of
  // the net's width); the net-ness of the declared object comes separately from
  // its own net keyword, not from the type_reference.
  for (const auto& n : mod->nets) {
    if (n.name != ref->text) continue;
    item->data_type.kind = DataTypeKind::kLogic;
    item->data_type.is_signed = n.is_signed;
    SetTypeRefPackedDims(item->data_type, n.width, arena_);
    item->data_type.type_ref_expr = nullptr;
    return;
  }
  auto it = var_types_.find(ref->text);
  if (it != var_types_.end()) {
    item->data_type.kind = it->second;
    item->data_type.type_ref_expr = nullptr;
  }
}

// The class a name reaches, or nothing when the answer is not clear.
//
// §8.1 lets a class be declared wherever a data declaration may appear, so the
// compilation unit's own list holds only the ones written at the top of a file
// and a lookup confined to it cannot see a class declared inside a module. What
// it must not do instead is guess: two modules may each declare a class of one
// name, and answering with whichever came first would resolve a rule against a
// class the source never named -- a wrong answer where there had only been
// silence. So a name declared once among the scopes is resolved, a name
// declared in more than one is left unresolved, and the caller is no worse off
// than it was.
static const ClassDecl* FindClassAmong(std::string_view name,
                                       const std::vector<ModuleItem*>& items) {
  for (const auto* item : items) {
    if (item != nullptr && item->kind == ModuleItemKind::kClassDecl &&
        item->class_decl != nullptr && item->class_decl->name == name) {
      return item->class_decl;
    }
  }
  return nullptr;
}

static void TakeUniqueMatch(const ClassDecl* found, const ClassDecl*& only,
                            bool& ambiguous) {
  if (found == nullptr) return;
  if (only != nullptr) ambiguous = true;
  only = found;
}

const ClassDecl* FindClassDecl(std::string_view name,
                               const CompilationUnit* unit) {
  for (const auto* cls : unit->classes) {
    if (cls->name == name) return cls;
  }
  const ClassDecl* only = nullptr;
  bool ambiguous = false;
  for (const auto* group :
       {&unit->modules, &unit->interfaces, &unit->programs, &unit->checkers}) {
    for (const auto* decl : *group) {
      TakeUniqueMatch(FindClassAmong(name, decl->items), only, ambiguous);
    }
  }
  for (const auto* pkg : unit->packages) {
    TakeUniqueMatch(FindClassAmong(name, pkg->items), only, ambiguous);
  }
  return ambiguous ? nullptr : only;
}

static const ModuleItem* FindClassTypedef(const ClassDecl* cls,
                                          std::string_view member_name) {
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kTypedef && m->name == member_name) {
      return m->typedef_item;
    }
  }
  return nullptr;
}

const DataType* FindClassScopedTypedefType(std::string_view cls_name,
                                           std::string_view type_name,
                                           const CompilationUnit* unit) {
  const auto* cls = FindClassDecl(cls_name, unit);
  if (cls == nullptr) return nullptr;
  const auto* td = FindClassTypedef(cls, type_name);
  if (td == nullptr) return nullptr;
  return &td->typedef_type;
}

// What each parameter of `cls` stands for in the specialization `args` writes,
// keyed by the parameter's own name.
//
// §23.10.2.2 (printed page 767) states that "parameter assignment by name
// consists of explicitly linking the parameter name and its new value", so a
// written name selects the formal whatever position the argument holds, and an
// argument written without one takes the position it holds. The same subclause
// states that "it is not necessary to assign values to all of the parameters
// ... Only parameters that are assigned new values need to be specified", so a
// formal the list does not mention keeps the default its declaration gave,
// which ClassDecl::param_types records. §8.25 (printed page 204) instantiates a
// specialization "using the same parameter override rules (see 23.10)", which
// is what brings all three to bear on a specialization.
//
// A formal declared with no default has a kImplicit entry in param_types and is
// left out, so a member reaching it fails to resolve rather than resolving to a
// type nothing named.
static std::unordered_map<std::string_view, const DataType*>
BuildSpecializationSubst(const ClassDecl* cls,
                         const std::vector<DataType>& args) {
  std::unordered_map<std::string_view, const DataType*> subst;
  for (size_t i = 0; i < args.size(); ++i) {
    if (!args[i].param_arg_name.empty()) {
      subst[args[i].param_arg_name] = &args[i];
    } else if (i < cls->params.size()) {
      subst[cls->params[i].first] = &args[i];
    }
  }
  const size_t defaults = std::min(cls->params.size(), cls->param_types.size());
  for (size_t i = 0; i < defaults; ++i) {
    if (cls->param_types[i].kind == DataTypeKind::kImplicit) continue;
    subst.emplace(cls->params[i].first, &cls->param_types[i]);
  }
  return subst;
}

bool ResolveParameterizedType(DataType& dtype, const CompilationUnit* unit) {
  if (dtype.scope_name.empty() || dtype.type_params.empty()) return false;
  const auto* cls = FindClassDecl(dtype.scope_name, unit);
  if (!cls) return false;
  auto subst = BuildSpecializationSubst(cls, dtype.type_params);

  // The scope resolution operator applied to a specialization may name a type
  // parameter of the class directly, or a member typedef whose aliased type is
  // one of those parameters. Resolve a direct type-parameter reference first;
  // otherwise look through a member typedef to the parameter it aliases.
  std::string_view param_name = dtype.type_name;
  if (!subst.count(param_name)) {
    const auto* td = FindClassTypedef(cls, dtype.type_name);
    if (!td) return false;
    param_name = td->typedef_type.type_name;
  }
  auto it = subst.find(param_name);
  if (it == subst.end()) return false;
  const DataType& resolved = *it->second;
  dtype.kind = resolved.kind;
  dtype.is_signed = resolved.is_signed;
  dtype.packed_dim_left = resolved.packed_dim_left;
  dtype.packed_dim_right = resolved.packed_dim_right;
  dtype.extra_packed_dims = resolved.extra_packed_dims;
  dtype.type_name = resolved.type_name;
  dtype.scope_name = {};
  dtype.type_params.clear();
  return true;
}

void Elaborator::ValidatePackedStructDefaults(const DataType& dtype,
                                              SourceLoc loc) {
  if (dtype.kind != DataTypeKind::kStruct || !dtype.is_packed) return;
  for (const auto& m : dtype.struct_members) {
    if (m.init_expr) {
      diag_.Error(loc,
                  "members of packed structures shall not be assigned "
                  "individual default member values",
                  Subclause("7.2.2"));
      return;
    }
  }
}

void Elaborator::ValidateUnpackedStructWithUnionDefaults(const DataType& dtype,
                                                         SourceLoc loc) {
  if (dtype.kind != DataTypeKind::kStruct || dtype.is_packed) return;
  bool has_union_member = false;
  for (const auto& m : dtype.struct_members) {
    if (m.type_kind == DataTypeKind::kUnion) has_union_member = true;
  }
  if (!has_union_member) return;
  for (const auto& m : dtype.struct_members) {
    if (m.init_expr) {
      diag_.Error(loc,
                  "members of unpacked structures containing a union shall "
                  "not be assigned individual default member values",
                  Subclause("7.2.2"));
      return;
    }
  }
}

void Elaborator::ValidateStructMemberDefaultsConstant(const DataType& dtype,
                                                      SourceLoc loc,
                                                      const ScopeMap& scope) {
  if (dtype.kind != DataTypeKind::kStruct) return;
  if (dtype.is_packed) return;
  for (const auto& m : dtype.struct_members) {
    if (m.type_kind == DataTypeKind::kUnion) return;
  }
  for (const auto& m : dtype.struct_members) {
    // §7.2.2: a member default is a constant expression, which per §11.2.1 may
    // reference a parameter. Use the module parameter scope (a superset of the
    // compilation-unit scope) so `int m = P;` resolves.
    if (m.init_expr && !IsConstantExpr(m.init_expr, scope)) {
      diag_.Error(loc,
                  "struct member default value must be a constant expression",
                  Subclause("7.2.2"));
      return;
    }
  }
}

void Elaborator::ValidateVoidMembers(const DataType& dtype, SourceLoc loc) {
  bool allow_void = (dtype.kind == DataTypeKind::kUnion && dtype.is_tagged);
  for (const auto& m : dtype.struct_members) {
    if (m.type_kind == DataTypeKind::kVoid && !allow_void) {
      diag_.Error(loc, "void member is only allowed in tagged unions",
                  Subclause("7.2"));
      return;
    }
  }
}

void Elaborator::ValidateRandQualifiers(const DataType& dtype, SourceLoc loc) {
  bool allow_rand = (dtype.kind == DataTypeKind::kStruct && !dtype.is_packed);
  for (const auto& m : dtype.struct_members) {
    if ((m.is_rand || m.is_randc) && !allow_rand) {
      diag_.Error(loc,
                  "random qualifier is only allowed in unpacked structures",
                  Subclause("7.2"));
      return;
    }
  }
}

void Elaborator::ValidatePackedDimRequiresPackedKeyword(const DataType& dtype,
                                                        SourceLoc loc) {
  if (dtype.kind != DataTypeKind::kStruct && dtype.kind != DataTypeKind::kUnion)
    return;
  if (!dtype.packed_dim_left) return;
  if (dtype.is_packed || dtype.is_soft) return;
  const char* kw = (dtype.kind == DataTypeKind::kStruct) ? "struct" : "union";
  diag_.Error(
      loc,
      std::format("packed dimension on {} requires the packed keyword", kw),
      Subclause("7.2"));
}

static bool IsLegalPackedMemberType(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kBit:
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
    case DataTypeKind::kByte:
    case DataTypeKind::kShortint:
    case DataTypeKind::kInt:
    case DataTypeKind::kLongint:
    case DataTypeKind::kInteger:
    case DataTypeKind::kTime:
    case DataTypeKind::kEnum:
    case DataTypeKind::kStruct:
    case DataTypeKind::kUnion:
    case DataTypeKind::kNamed:
    case DataTypeKind::kImplicit:
      return true;
    default:
      return false;
  }
}

void Elaborator::ValidatePackedStructMemberTypes(const DataType& dtype,
                                                 SourceLoc loc) {
  if (!dtype.is_packed && !dtype.is_soft) return;
  if (dtype.kind != DataTypeKind::kStruct && dtype.kind != DataTypeKind::kUnion)
    return;
  const char* container = (dtype.kind == DataTypeKind::kStruct)
                              ? "packed structure"
                              : "packed union";
  // §7.3.2: a void member is legal in a packed tagged union — it carries no
  // value bits, and in that extreme case only the tag is significant while the
  // remaining bits are undefined (the packed VInt example). A void member
  // elsewhere is already barred by ValidateVoidMembers, so it need only be
  // exempted from the packed-member-type check for the tagged-union case.
  bool tagged_union = dtype.kind == DataTypeKind::kUnion && dtype.is_tagged;
  for (const auto& m : dtype.struct_members) {
    if (m.type_kind == DataTypeKind::kVoid && tagged_union) continue;
    if (!IsLegalPackedMemberType(m.type_kind)) {
      diag_.Error(loc,
                  std::format("type of member '{}' is not allowed in a {}",
                              m.name, container),
                  Subclause("7.2.1"));
      continue;
    }
    // §7.2.1: only packed data types are permitted as members. A member that
    // carries unpacked dimensions is an unpacked array, which is not a packed
    // type, so it cannot appear in a packed structure or union.
    if (!m.unpacked_dims.empty()) {
      diag_.Error(
          loc,
          std::format("unpacked array member '{}' is not allowed in a {}",
                      m.name, container),
          Subclause("7.2.1"));
    }
  }
}

void Elaborator::ValidateChandleInUnion(const DataType& dtype, SourceLoc loc) {
  if (dtype.kind != DataTypeKind::kUnion) return;
  if (dtype.is_tagged) return;
  // §7.3.2 carries the obligation this enforces: "Dynamic types and chandle
  // types shall not be used in untagged unions, but may be used in tagged
  // unions." §7.3 states the same fact as descriptive prose and states no
  // obligation, so the report names the subclause that does.
  for (const auto& m : dtype.struct_members) {
    if (m.type_kind == DataTypeKind::kChandle) {
      diag_.Error(loc, "chandle type can only be used in tagged unions",
                  Subclause("7.3.2"));
      return;
    }
    if (m.type_kind == DataTypeKind::kString) {
      diag_.Error(loc, "string type can only be used in tagged unions",
                  Subclause("7.3.2"));
      return;
    }
    if (m.type_kind == DataTypeKind::kEvent) {
      diag_.Error(loc, "event type can only be used in tagged unions",
                  Subclause("7.3.2"));
      return;
    }
  }
}

void Elaborator::ValidateVirtualInterfaceInUnion(const DataType& dtype,
                                                 SourceLoc loc) {
  if (dtype.kind != DataTypeKind::kUnion) return;
  for (const auto& m : dtype.struct_members) {
    if (m.type_kind == DataTypeKind::kVirtualInterface) {
      diag_.Error(loc,
                  "virtual interface cannot be used as a member of a union",
                  Subclause("25.9"));
      return;
    }
  }
}

void Elaborator::ValidatePackedUnion(const DataType& dtype, SourceLoc loc) {
  if (dtype.kind != DataTypeKind::kUnion) return;
  if (!dtype.is_packed && !dtype.is_soft) return;
  if (dtype.struct_members.empty()) return;
  if (!dtype.is_soft && !dtype.is_tagged) {
    uint32_t first_w =
        EvalStructMemberWidth(dtype.struct_members[0], typedefs_);
    for (size_t i = 1; i < dtype.struct_members.size(); ++i) {
      uint32_t w = EvalStructMemberWidth(dtype.struct_members[i], typedefs_);
      if (w != first_w) {
        diag_.Error(loc,
                    std::format("packed union member '{}' has width {} but "
                                "first member '{}' has width {}",
                                dtype.struct_members[i].name, w,
                                dtype.struct_members[0].name, first_w),
                    Subclause("7.3.1"));
      }
    }
  }
}

}  // namespace delta
