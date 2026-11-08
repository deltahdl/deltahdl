#pragma once

#include <cstdint>
#include <string>
#include <string_view>

namespace delta {

class Arena;
struct ClassObject;
struct ClassTypeInfo;
struct Expr;
struct Logic4Vec;
struct QueueObject;
class SimContext;
struct StructFieldInfo;
struct StructTypeInfo;
struct Variable;

struct StructArrayElementRef {
  Logic4Vec* value = nullptr;
  Variable* var = nullptr;
  uint32_t bit_offset = 0;
  uint32_t width = 0;
  bool is_signed = false;
  bool is_string = false;
  bool in_range = false;
};

bool ResolveStructArrayElement(const Expr* select, SimContext& ctx,
                               Arena& arena, StructArrayElementRef& out);

const StructFieldInfo* ResolveStructArrayMember(const Expr* access,
                                                SimContext& ctx);

const StructTypeInfo* ContainerElementLayout(const Expr* base, SimContext& ctx);

bool TryContainerElementMember(const Expr* expr, SimContext& ctx, Arena& arena,
                               Logic4Vec& out);

Logic4Vec NonexistentAggregateElement(const StructTypeInfo& layout,
                                      SimContext& ctx, Arena& arena);

struct PackedMemberBits {
  std::string_view prop;
  uint32_t offset = 0;
  uint32_t width = 0;
};

bool PropertyPackedMemberBits(const Expr* access, const ClassObject* obj,
                              SimContext& ctx, PackedMemberBits& out);

const StructTypeInfo* StructLayoutOfOperand(const Expr* e, SimContext& ctx);

QueueObject* ResolveStructDynMember(const Expr* access, SimContext& ctx,
                                    Arena& arena, bool write);

const StructFieldInfo* ResolveStructMember(const Expr* access, SimContext& ctx);

bool MemberIsTwoState(const StructFieldInfo& f, SimContext& ctx);

const StructTypeInfo* TaggedMemberLayout(const StructTypeInfo& sinfo,
                                         std::string_view member);

struct StaticPropertyRef {
  const ClassTypeInfo* owner = nullptr;
  Logic4Vec* slot = nullptr;
  std::string_view name;
};

bool ResolveStaticPropertyBase(const Expr* base, SimContext& ctx, Arena& arena,
                               StaticPropertyRef& out);

ClassObject* StaticPropertyObject(const StaticPropertyRef& ref, SimContext& ctx,
                                  std::string_view* declared_key);

bool ResolveStaticHandlePath(const Expr* access, SimContext& ctx, Arena& arena,
                             StaticPropertyRef& ref, std::string& path);

bool TryStaticHandleMember(const Expr* expr, SimContext& ctx, Arena& arena,
                           Logic4Vec& out);

}  // namespace delta
