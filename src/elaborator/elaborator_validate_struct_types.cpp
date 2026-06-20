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

void Elaborator::ResolveTypeRef(ModuleItem* item, const RtlirModule* mod) {
  if (!item->data_type.type_ref_expr) return;
  auto* ref = item->data_type.type_ref_expr;
  CheckTypeRefArgInner(ref, item->loc);
  if (ref->kind != ExprKind::kIdentifier) {
    uint32_t w = InferTypeRefExprWidth(ref, mod);
    item->data_type.kind = DataTypeKind::kLogic;
    if (w > 1) {
      auto* left = arena_.Create<Expr>();
      left->kind = ExprKind::kIntegerLiteral;
      left->int_val = static_cast<int64_t>(w - 1);
      auto* right = arena_.Create<Expr>();
      right->kind = ExprKind::kIntegerLiteral;
      right->int_val = 0;
      item->data_type.packed_dim_left = left;
      item->data_type.packed_dim_right = right;
    }
    item->data_type.is_signed = InferTypeRefExprSigned(ref, mod);
    item->data_type.type_ref_expr = nullptr;
    return;
  }
  for (const auto& v : mod->variables) {
    if (v.name != ref->text) continue;
    item->data_type.kind = var_types_[ref->text];
    item->data_type.is_signed = v.is_signed;
    if (v.width > 1 && (item->data_type.kind == DataTypeKind::kLogic ||
                        item->data_type.kind == DataTypeKind::kBit ||
                        item->data_type.kind == DataTypeKind::kReg)) {
      auto* left = arena_.Create<Expr>();
      left->kind = ExprKind::kIntegerLiteral;
      left->int_val = static_cast<int64_t>(v.width - 1);
      auto* right = arena_.Create<Expr>();
      right->kind = ExprKind::kIntegerLiteral;
      right->int_val = 0;
      item->data_type.packed_dim_left = left;
      item->data_type.packed_dim_right = right;
    }
    item->data_type.type_ref_expr = nullptr;
    return;
  }
  auto it = var_types_.find(ref->text);
  if (it != var_types_.end()) {
    item->data_type.kind = it->second;
    item->data_type.type_ref_expr = nullptr;
  }
}

const ClassDecl* FindClassDecl(std::string_view name,
                               const CompilationUnit* unit) {
  for (const auto* cls : unit->classes) {
    if (cls->name == name) return cls;
  }
  return nullptr;
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

bool Elaborator::ResolveParameterizedType(DataType& dtype) {
  if (dtype.scope_name.empty() || dtype.type_params.empty()) return false;
  const auto* cls = FindClassDecl(dtype.scope_name, unit_);
  if (!cls) return false;
  std::unordered_map<std::string_view, const DataType*> subst;
  for (size_t i = 0; i < cls->params.size() && i < dtype.type_params.size();
       ++i) {
    subst[cls->params[i].first] = &dtype.type_params[i];
  }

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
                  "individual default member values");
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
                  "not be assigned individual default member values");
      return;
    }
  }
}

void Elaborator::ValidateStructMemberDefaultsConstant(const DataType& dtype,
                                                      SourceLoc loc) {
  if (dtype.kind != DataTypeKind::kStruct) return;
  if (dtype.is_packed) return;
  for (const auto& m : dtype.struct_members) {
    if (m.type_kind == DataTypeKind::kUnion) return;
  }
  for (const auto& m : dtype.struct_members) {
    if (m.init_expr && !IsConstantExpr(m.init_expr, cu_param_scope_)) {
      diag_.Error(loc,
                  "struct member default value must be a constant expression");
      return;
    }
  }
}

void Elaborator::ValidateVoidMembers(const DataType& dtype, SourceLoc loc) {
  bool allow_void = (dtype.kind == DataTypeKind::kUnion && dtype.is_tagged);
  for (const auto& m : dtype.struct_members) {
    if (m.type_kind == DataTypeKind::kVoid && !allow_void) {
      diag_.Error(loc, "void member is only allowed in tagged unions");
      return;
    }
  }
}

void Elaborator::ValidateRandQualifiers(const DataType& dtype, SourceLoc loc) {
  bool allow_rand = (dtype.kind == DataTypeKind::kStruct && !dtype.is_packed);
  for (const auto& m : dtype.struct_members) {
    if ((m.is_rand || m.is_randc) && !allow_rand) {
      diag_.Error(loc,
                  "random qualifier is only allowed in unpacked structures");
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
      std::format("packed dimension on {} requires the packed keyword", kw));
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
  for (const auto& m : dtype.struct_members) {
    if (!IsLegalPackedMemberType(m.type_kind)) {
      diag_.Error(loc, std::format("type of member '{}' is not allowed in a {}",
                                   m.name, container));
    }
  }
}

void Elaborator::ValidateChandleInUnion(const DataType& dtype, SourceLoc loc) {
  if (dtype.kind != DataTypeKind::kUnion) return;
  if (dtype.is_tagged) return;
  for (const auto& m : dtype.struct_members) {
    if (m.type_kind == DataTypeKind::kChandle) {
      diag_.Error(loc, "chandle type can only be used in tagged unions");
      return;
    }
    if (m.type_kind == DataTypeKind::kString) {
      diag_.Error(loc, "string type can only be used in tagged unions");
      return;
    }
    if (m.type_kind == DataTypeKind::kEvent) {
      diag_.Error(loc, "event type can only be used in tagged unions");
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
                  "virtual interface cannot be used as a member of a union");
      return;
    }
  }
}

void Elaborator::ValidatePackedUnion(const DataType& dtype, SourceLoc loc) {
  if (dtype.kind != DataTypeKind::kUnion) return;
  if (!dtype.is_packed && !dtype.is_soft) return;
  if (dtype.struct_members.empty()) return;
  if (!dtype.is_soft && !dtype.is_tagged) {
    uint32_t first_w = EvalStructMemberWidth(dtype.struct_members[0]);
    for (size_t i = 1; i < dtype.struct_members.size(); ++i) {
      uint32_t w = EvalStructMemberWidth(dtype.struct_members[i]);
      if (w != first_w) {
        diag_.Error(loc,
                    std::format("packed union member '{}' has width {} but "
                                "first member '{}' has width {}",
                                dtype.struct_members[i].name, w,
                                dtype.struct_members[0].name, first_w));
      }
    }
  }
}

}  // namespace delta
