#include <cmath>
#include <cstdint>
#include <format>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

void Elaborator::ElaborateTypedef(ModuleItem* item, RtlirModule* mod) {
  static const auto kIndName = [](DataTypeKind k) -> std::string_view {
    switch (k) {
      case DataTypeKind::kEnum:
        return "enum";
      case DataTypeKind::kStruct:
        return "struct";
      case DataTypeKind::kUnion:
        return "union";
      default:
        return "type";
    }
  };
  bool is_forward = item->typedef_type.kind == DataTypeKind::kImplicit;
  if (is_forward) {
    if (item->forward_type_kind != DataTypeKind::kImplicit) {
      auto td_it = typedefs_.find(item->name);
      if (td_it != typedefs_.end() &&
          td_it->second.kind != DataTypeKind::kImplicit &&
          td_it->second.kind != item->forward_type_kind) {
        diag_.Error(item->loc,
                    std::format("forward typedef '{}' as {} does not conform "
                                "to its existing definition",
                                item->name, kIndName(item->forward_type_kind)));
      }
      forward_typedef_kinds_[item->name] = item->forward_type_kind;
    }

    typedefs_.try_emplace(item->name, item->typedef_type);
    return;
  }
  auto it = forward_typedef_kinds_.find(item->name);
  if (it != forward_typedef_kinds_.end() &&
      it->second != item->typedef_type.kind) {
    diag_.Error(item->loc,
                std::format("typedef '{}' does not conform to its forward "
                            "declaration as {}",
                            item->name, kIndName(it->second)));
  }
  typedefs_[item->name] = item->typedef_type;
  // §6.24.3: track typedefs whose first unpacked dimension is an associative
  // index, so the bit-stream cast validator can reject them as destinations.
  bool first_dim_assoc = false;
  if (!item->unpacked_dims.empty() && item->unpacked_dims[0] &&
      item->unpacked_dims[0]->kind == ExprKind::kIdentifier) {
    auto t = item->unpacked_dims[0]->text;
    if (t == "string" || t == "int" || t == "integer" || t == "byte" ||
        t == "shortint" || t == "longint" || t == "*") {
      assoc_typedef_names_.insert(item->name);
      first_dim_assoc = true;
    } else if (typedefs_.count(t) > 0 || class_names_.count(t) > 0) {
      assoc_typedef_names_.insert(item->name);
      first_dim_assoc = true;
    }
  }
  // §6.24.3: when every unpacked dimension is a fixed integer size (no
  // dynamic, queue, or associative dim), the typedef has a known total bit
  // width that the bit-stream cast validator can compare against a source.
  if (!item->unpacked_dims.empty() && !first_dim_assoc) {
    uint32_t elem_width = EvalTypeWidth(item->typedef_type, typedefs_);
    uint64_t total = elem_width;
    bool all_fixed = (elem_width > 0);
    for (auto* dim : item->unpacked_dims) {
      if (!dim) {
        all_fixed = false;
        break;
      }
      if (dim->kind == ExprKind::kIdentifier) {
        auto t = dim->text;
        if (t == "$" || t == "*" || t == "string" || t == "int" ||
            t == "integer" || t == "byte" || t == "shortint" ||
            t == "longint") {
          all_fixed = false;
          break;
        }
      }
      if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
        auto lv = ConstEvalInt(dim->lhs);
        auto rv = ConstEvalInt(dim->rhs);
        if (!lv || !rv) {
          all_fixed = false;
          break;
        }
        int64_t span = std::abs(*lv - *rv) + 1;
        total *= static_cast<uint64_t>(span);
      } else {
        auto sv = ConstEvalInt(dim);
        if (!sv || *sv <= 0) {
          all_fixed = false;
          break;
        }
        total *= static_cast<uint64_t>(*sv);
      }
    }
    if (all_fixed && total > 0 && total < uint64_t{1} << 32) {
      fixed_unpacked_typedef_widths_[item->name] = static_cast<uint32_t>(total);
    }
  }
  if (item->typedef_type.kind == DataTypeKind::kStruct ||
      item->typedef_type.kind == DataTypeKind::kUnion) {
    ValidatePackedStructDefaults(item->typedef_type, item->loc);
    ValidateUnpackedStructWithUnionDefaults(item->typedef_type, item->loc);
    ValidateStructMemberDefaultsConstant(item->typedef_type, item->loc);
    ValidateVoidMembers(item->typedef_type, item->loc);
    ValidateRandQualifiers(item->typedef_type, item->loc);
    ValidatePackedDimRequiresPackedKeyword(item->typedef_type, item->loc);
    ValidatePackedStructMemberTypes(item->typedef_type, item->loc);
    ValidateChandleInUnion(item->typedef_type, item->loc);
    ValidateVirtualInterfaceInUnion(item->typedef_type, item->loc);
    ValidatePackedUnion(item->typedef_type, item->loc);
  }
  ValidatePackedDimOnPredefinedType(item->typedef_type, item->loc);
  ValidatePackedDimOnDisallowedType(item->typedef_type, item->loc);
  if (item->typedef_type.kind != DataTypeKind::kEnum) return;
  ValidateEnumDecl(item->typedef_type, item->loc);
  int64_t next_val = 0;
  auto width = EvalTypeWidth(item->typedef_type, typedefs_);
  std::vector<RtlirEnumMember> members;
  // Records one enum member (name + current value), reserving its name and
  // emitting a backing variable, then advances the running value.
  auto emit_member = [&](std::string_view name) {
    enum_member_names_.insert(name);
    members.push_back({name, next_val});
    RtlirVariable var;
    var.name = name;
    var.width = width;
    var.is_4state = false;
    mod->variables.push_back(var);
    ++next_val;
  };
  // Builds an arena-owned "<base><index>" name and emits it as a member.
  auto emit_indexed_member = [&](std::string_view base, int64_t index) {
    auto s = std::format("{}{}", base, index);
    auto* p = arena_.AllocString(s.c_str(), s.size());
    emit_member(std::string_view{p, s.size()});
  };
  for (const auto& member : item->typedef_type.enum_members) {
    if (member.value) {
      next_val = ConstEvalInt(member.value).value_or(next_val);
    }

    if (member.range_start) {
      auto n = ConstEvalInt(member.range_start).value_or(0);
      if (member.range_end) {
        auto m = ConstEvalInt(member.range_end).value_or(0);
        int step = (m >= n) ? 1 : -1;
        for (auto i = n;; i += step) {
          emit_indexed_member(member.name, i);
          if (i == m) break;
        }
      } else {
        for (int64_t i = 0; i < n; ++i) {
          emit_indexed_member(member.name, i);
        }
      }
    } else {
      emit_member(member.name);
    }
  }
  mod->enum_types[item->name] = std::move(members);
}

void Elaborator::ElaborateNettypeDecl(ModuleItem* item, RtlirModule*) {
  typedefs_[item->name] = item->typedef_type;
  nettype_names_.insert(item->name);
  if (!item->nettype_resolve_func.empty()) {
    nettype_resolve_funcs_[item->name] = item->nettype_resolve_func;
    nettype_canonical_[item->name] = item->name;
  } else if (item->typedef_type.kind == DataTypeKind::kNamed) {
    auto it = nettype_resolve_funcs_.find(item->typedef_type.type_name);
    if (it != nettype_resolve_funcs_.end()) {
      nettype_resolve_funcs_[item->name] = it->second;
    }

    auto cit = nettype_canonical_.find(item->typedef_type.type_name);
    nettype_canonical_[item->name] = (cit != nettype_canonical_.end())
                                         ? cit->second
                                         : item->typedef_type.type_name;
  } else {
    nettype_canonical_[item->name] = item->name;
  }
}

// §6.22.6 Matching nettypes: a nettype matches itself (and the nettype of nets
// declared using it), and a simple nettype that renames a user-defined nettype
// matches the nettype it renames. Both cases reduce to comparing the canonical
// (source) nettype each name resolves to: an alias shares its source's
// canonical name, so it matches; unrelated nettypes have distinct canonical
// names, so they do not.
bool NettypesMatch(std::string_view a, std::string_view b,
                   const std::unordered_map<std::string_view, std::string_view>&
                       nettype_canonical) {
  if (a == b) return true;
  auto ait = nettype_canonical.find(a);
  auto bit = nettype_canonical.find(b);
  std::string_view ca = (ait != nettype_canonical.end()) ? ait->second : a;
  std::string_view cb = (bit != nettype_canonical.end()) ? bit->second : b;
  return ca == cb;
}

}  // namespace delta
