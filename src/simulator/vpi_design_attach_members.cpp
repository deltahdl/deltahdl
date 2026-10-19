#include <algorithm>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/packed_range.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "parser/ast_class.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_attach_vars.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

int VpiDataTypeVariableKind(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kByte:
      return vpiByteVar;
    case DataTypeKind::kShortint:
      return vpiShortIntVar;
    case DataTypeKind::kInt:
      return vpiIntVar;
    case DataTypeKind::kLongint:
      return vpiLongIntVar;
    case DataTypeKind::kInteger:
      return vpiIntegerVar;
    case DataTypeKind::kTime:
      return vpiTimeVar;
    case DataTypeKind::kBit:
      return vpiBitVar;
    case DataTypeKind::kStruct:
      return vpiStructVar;
    case DataTypeKind::kUnion:
      return vpiUnionVar;
    // §6.12 makes realtime a synonym for real.
    case DataTypeKind::kReal:
    case DataTypeKind::kRealtime:
      return vpiRealVar;
    case DataTypeKind::kShortreal:
      return vpiShortRealVar;
    case DataTypeKind::kString:
      return vpiStringVar;
    case DataTypeKind::kChandle:
      return vpiChandleVar;
    case DataTypeKind::kEnum:
      return vpiEnumVar;
    // §37.27 and §37.29.
    case DataTypeKind::kEvent:
      return vpiNamedEvent;
    case DataTypeKind::kVirtualInterface:
      return vpiVirtualInterfaceVar;
    default:
      return kVpiReg;
  }
}

namespace {

// §8.3, §9.7, §15.3 and §15.4: whether `name` names a class a scope sees:
// one of `classes`, those the scope declares, one the compilation unit
// declares, or one of the built-in classes.
bool NamesClass(const RtlirDesign& design,
                const std::vector<ClassDecl*>& classes, std::string_view name) {
  static constexpr std::string_view kBuiltIn[] = {"process", "semaphore",
                                                  "mailbox"};
  const auto kIsNamed = [name](std::string_view cls) { return cls == name; };
  const auto kDeclares = [&](const std::vector<ClassDecl*>& decls) {
    return std::ranges::any_of(decls, [&](const ClassDecl* decl) {
      return decl != nullptr && kIsNamed(decl->name);
    });
  };
  return kDeclares(classes) || kDeclares(design.cu_class_decls) ||
         std::ranges::any_of(kBuiltIn, kIsNamed);
}

// §6.18 with §8.3: the object kind of a variable of a type that is a class
// where `names_class`, and otherwise the one the typedef the design records
// under `key` stands for, a class where its chain of names ends in one.
int NamedTypeKind(const RtlirDesign& design, bool names_class,
                  std::string_view key) {
  if (names_class || design.type_targets.contains(key)) return vpiClassVar;
  const auto kFound = design.type_kinds.find(key);
  if (kFound == design.type_kinds.end()) return kVpiReg;
  return VpiDataTypeVariableKind(kFound->second);
}

}  // namespace

int VpiNamedTypeVariableKind(const RtlirDesign& design, const RtlirModule& mod,
                             std::string_view name) {
  return NamedTypeKind(design, NamesClass(design, mod.class_decls, name), name);
}

std::vector<ClassDecl*> VpiPackageClasses(const PackageDecl& package) {
  std::vector<ClassDecl*> classes;
  for (const ModuleItem* item : package.items) {
    if (item->kind == ModuleItemKind::kClassDecl) {
      classes.push_back(item->class_decl);
    }
  }
  return classes;
}

int VpiPackageNamedTypeVariableKind(const RtlirDesign& design,
                                    const PackageDecl* package,
                                    std::string_view name) {
  if (package == nullptr) {
    return NamedTypeKind(design, NamesClass(design, {}, name), name);
  }
  return NamedTypeKind(design,
                       NamesClass(design, VpiPackageClasses(*package), name),
                       std::string(package->name) + "::" + std::string(name));
}

namespace {

// §37.26: the member of `holder` the field `field` lays out: its vpiParent is
// the struct or union var or net, it is named after the field, its kind is a
// net for a net's member and otherwise the one a variable of the field's type
// has (§37.17), and its value is the field's bits of the holder's value, a
// copy that a read refreshes and a write is copied back from, read as a real
// where the field is one.
VpiObject* MakeMember(VpiObject* holder, const StructFieldInfo& field,
                      const RtlirDesign& design, const RtlirModule& mod,
                      const VpiAttachBuild& build) {
  VpiObject* member = build.alloc();
  if (holder->type == vpiStructNet || holder->type == vpiUnionNet) {
    member->type = kVpiNet;
  } else if (field.type_kind == DataTypeKind::kNamed) {
    member->type = VpiNamedTypeVariableKind(design, mod, field.type_name);
  } else {
    member->type = VpiDataTypeVariableKind(field.type_kind);
  }
  member->parent = holder;
  member->name = build.keep(std::string(field.name));
  member->full_name = holder->full_name + "." + std::string(field.name);
  member->decl_signed = field.is_signed;
  // §37.17 detail 20: a member is a scalar or a vector as a variable of its
  // field's type is, a bit or logic field wider than one bit having a packed
  // dimension, and one declared as an unpacked array answers as its element.
  VpiScalarVectorQuery shape;
  shape.var_type = member->type;
  shape.has_packed_dimension =
      (field.elem_count != 0 ? field.width / field.elem_count : field.width) >
      1;
  member->decl_scalar = VpiVariableScalar(shape);
  member->decl_vector = VpiVariableVector(shape);
  auto* storage = build.arena.Create<Variable>();
  storage->value = MakeLogic4Vec(build.arena, field.width);
  storage->value.is_signed = field.is_signed;
  storage->value.is_real =
      member->type == vpiRealVar || member->type == vpiShortRealVar;
  member->var = storage;
  member->size = static_cast<int>(field.width);
  member->member_of = holder;
  member->member_offset = field.bit_offset;
  holder->children.push_back(member);
  return member;
}

// §37.17 detail 12 with §7.4.1: the dimensions the bits of `member`, of the
// field `field`, are indexed by: a bit or logic member's packed ones, the
// outermost as the layout records it over its elements' own [n-1:0], and a
// packed structure's or union's implicit [n-1:0] (§7.2.1). None for a net's
// member, a member of one bit, an unpacked array or dynamic member, or one of
// any other type.
std::optional<PackedDims> MemberBitDims(const VpiObject& member,
                                        const StructFieldInfo& field) {
  const bool kVector = member.type == kVpiReg || member.type == vpiBitVar;
  const bool kPacked = field.nested != nullptr && field.nested->is_packed;
  if (!VpiIsVariablesType(member.type) || field.width <= 1 ||
      field.elem_count != 0 || field.is_dynamic || (!kVector && !kPacked)) {
    return std::nullopt;
  }
  if (kVector && field.packed_elem_width != 0) {
    return PackedDims{PackedRange{field.packed_left, field.packed_right},
                      PackedRange::Implicit(field.packed_elem_width)};
  }
  return PackedDims{PackedRange::Implicit(field.width)};
}

// §37.17 details 2, 18 and 26: a member `array` of the field `field`, declared
// with an unpacked dimension, made the array var it is, with an element per
// index of the dimension, left index first, each a variable of the member's
// type that the array's members are, carrying its index and holding its bits
// of the outermost structure, where the layout puts the leftmost element in
// the most significant ones.
void MakeMemberElements(VpiObject* array, const StructFieldInfo& field,
                        const VpiAttachBuild& build) {
  const int kElementType = array->type;
  const uint32_t kWidth = field.width / field.elem_count;
  array->type = vpiArrayVar;
  array->array_type = vpiStaticArray;
  array->size = static_cast<int>(field.elem_count);
  std::vector<int>& indices = array->array_dim_indices.emplace_back();
  const int64_t kStep = field.elem_left <= field.elem_right ? 1 : -1;
  for (uint32_t position = 0; position < field.elem_count; ++position) {
    const int64_t kIndex = field.elem_left + (kStep * position);
    const std::string kSuffix = "[" + std::to_string(kIndex) + "]";
    VpiObject* element = build.alloc();
    element->type = kElementType;
    element->parent = array;
    element->name = build.keep(std::string(array->name) + kSuffix);
    element->full_name = array->full_name + kSuffix;
    element->array_member = true;
    element->index = static_cast<int>(kIndex);
    element->index_expr = VpiIntConstant(kIndex, build);
    element->children.push_back(element->index_expr);
    element->decl_signed = array->decl_signed;
    element->decl_scalar = array->decl_scalar;
    element->decl_vector = array->decl_vector;
    auto* storage = build.arena.Create<Variable>();
    storage->value = MakeLogic4Vec(build.arena, kWidth);
    storage->value.is_signed = field.is_signed;
    element->var = storage;
    element->size = static_cast<int>(kWidth);
    element->member_of = array->member_of;
    element->member_offset =
        array->member_offset + ((field.elem_count - 1 - position) * kWidth);
    array->children.push_back(element);
    indices.push_back(static_cast<int>(kIndex));
  }
}

// What the members of one instance are made from: its module, the objects
// keyed under its name `prefix`, and what a run builds with.
struct MemberSite {
  const RtlirDesign& design;
  const RtlirModule& mod;
  const std::string& prefix;
  const VpiObjectMap& objects;
  SimContext& ctx;
  const VpiAttachBuild& build;
};

// The member per field of the layout `info` gives `holder`. §37.17 detail 28's
// example names `str1.inner1.j1`: a member of a structure or union type has a
// member per field of its own, each read from and written back to the storage
// of the outermost structure, at its offset there, as each member's bits are
// (detail 12).
void MakeMembers(VpiObject* holder, const StructTypeInfo& info,
                 const MemberSite& site) {
  for (const StructFieldInfo& field : info.fields) {
    VpiObject* member =
        MakeMember(holder, field, site.design, site.mod, site.build);
    if (holder->member_of != nullptr) {
      member->member_of = holder->member_of;
      member->member_offset += holder->member_offset;
    }
    if (field.elem_count != 0 && VpiIsVariablesType(member->type)) {
      MakeMemberElements(member, field, site.build);
    } else if (field.nested != nullptr) {
      MakeMembers(member, *field.nested, site);
    }
    if (const std::optional<PackedDims> kDims = MemberBitDims(*member, field)) {
      VpiMakeMemberBits(*member, *kDims, site.build);
    }
  }
}

// §37.17 detail 26: an element of an array of structures or unions is a
// struct or union var of its own, `spa[9][12]`, with a member per field of
// the array's layout, each reached through the element. The leaves of the
// array the elements pass made are those elements.
void MakeElementMembers(VpiObject* array, const StructTypeInfo& info,
                        const MemberSite& site) {
  for (VpiObject* element : array->children) {
    if (!element->array_member) continue;
    if (VpiIsArrayVarType(element->type)) {
      MakeElementMembers(element, info, site);
    } else if (element->var != nullptr) {
      element->type = info.is_union ? vpiUnionVar : vpiStructVar;
      element->packed = info.is_packed;
      MakeMembers(element, info, site);
    }
  }
}

// §37.17 details 3, 17 and 26: a struct or union var, packed or not, has a
// member variable per field, the struct as its vpiParent and the field's value
// as its own. The run keeps the whole struct as one variable, and no member
// object was made, so vpiMember reached nothing and no name reached a field; a
// packed one was passed over after that, though §37.26 makes vpiPacked only a
// property of the struct var.
void AttachVariableMembers(const MemberSite& site) {
  for (const RtlirVariable& var : site.mod.variables) {
    const std::string kKey = VpiFlatName(site.prefix, var.name);
    VpiObject* holder = FindObjectForFlatName(site.objects, kKey);
    const StructTypeInfo* info = site.ctx.GetVariableStructType(kKey);
    if (holder == nullptr || info == nullptr) continue;
    if (VpiIsArrayVarType(holder->type)) {
      MakeElementMembers(holder, *info, site);
    } else if (holder->var != nullptr &&
               (holder->type == vpiStructVar || holder->type == vpiUnionVar)) {
      MakeMembers(holder, *info, site);
    }
  }
}

// §37.26: a net of a structure or union type is a struct net or a union net,
// with a member net per field. Every net of the run is an object
// (VpiContext::Attach), and the run registers the layout of each one of an
// aggregate type under the same key (RegisterAggregateLayout); each reported
// vpiNet and held no member.
void AttachNetMembers(const MemberSite& site) {
  for (const RtlirNet& net : site.mod.nets) {
    const std::string kKey = VpiFlatName(site.prefix, net.name);
    const StructTypeInfo* info = site.ctx.GetVariableStructType(kKey);
    if (info == nullptr) continue;
    VpiObject* holder = FindObjectForFlatName(site.objects, kKey);
    holder->type = info->is_union ? vpiUnionNet : vpiStructNet;
    MakeMembers(holder, *info, site);
  }
}

}  // namespace

int VpiNetObjectKind(const RtlirNet& net) {
  // §37.24 (figure): a generic interconnect is an interconnect net, which has
  // no data type of its own.
  if (net.net_type == NetType::kInterconnect) return vpiInterconnectNet;
  switch (net.data_kind) {
    // §37.16 detail 1: a packed struct, union or enum net with a packed
    // dimension of its own is a packed array net.
    case DataTypeKind::kStruct:
      return net.has_declared_packed_dim ? vpiPackedArrayNet : vpiStructNet;
    case DataTypeKind::kUnion:
      return net.has_declared_packed_dim ? vpiPackedArrayNet : vpiUnionNet;
    case DataTypeKind::kEnum:
      return net.has_declared_packed_dim ? vpiPackedArrayNet : vpiEnumNet;
    case DataTypeKind::kInteger:
      return vpiIntegerNet;
    case DataTypeKind::kTime:
      return vpiTimeNet;
    // §6.7.1 keeps a 2-state or real type off a built-in net type, so these
    // arise through a user-defined nettype (§6.6.7), the figure's user
    // defined net.
    case DataTypeKind::kBit:
      return vpiBitNet;
    case DataTypeKind::kByte:
      return vpiByteNet;
    case DataTypeKind::kShortint:
      return vpiShortIntNet;
    case DataTypeKind::kInt:
      return vpiIntNet;
    case DataTypeKind::kLongint:
      return vpiLongIntNet;
    case DataTypeKind::kReal:
    case DataTypeKind::kRealtime:
      return vpiRealNet;
    case DataTypeKind::kShortreal:
      return vpiShortRealNet;
    default:
      return kVpiNet;
  }
}

void RecordNetObjectKinds(const RtlirDesign* design,
                          const VpiObjectMap& objects) {
  // §37.16 (figure): a net is drawn as the kind its data type makes it. The run
  // made every net a logic net, and only a struct or union net with a layout
  // of its own was told otherwise (AttachNetMembers), so no design had an enum
  // net, an integer net or a packed array net.
  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        for (const RtlirNet& net : VpiDeclaredNets(*mod)) {
          const int kKind = VpiNetObjectKind(net);
          for (const std::string& key : VpiDeclaredNetKeys(net, prefix)) {
            VpiObject* obj = FindObjectForFlatName(objects, key);
            if (obj != nullptr && obj->type == kVpiNet) obj->type = kKind;
          }
        }
      });
}

void AttachStructMembers(const RtlirDesign* design, const VpiObjectMap& objects,
                         SimContext& ctx, const VpiAttachBuild& build) {
  if (design == nullptr) return;
  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        const MemberSite kSite{*design, *mod, prefix, objects, ctx, build};
        AttachVariableMembers(kSite);
        AttachNetMembers(kSite);
      });
}

}  // namespace delta
