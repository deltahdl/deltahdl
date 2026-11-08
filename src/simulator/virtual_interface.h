#pragma once

#include <cstdint>
#include <string>
#include <string_view>

namespace delta {

class Arena;
class SimContext;
struct DataType;
struct Expr;
struct Logic4Vec;
struct SourceLoc;

inline constexpr uint64_t kNullVirtualInterface = 0;

struct VirtualInterfaceBase {
  bool is_virtual_interface = false;
  uint64_t handle = kNullVirtualInterface;
};

bool DeclaresAVirtualInterface(const DataType& type, const SimContext& ctx);

VirtualInterfaceBase ResolveVirtualInterfaceBase(std::string_view name,
                                                 SimContext& ctx, Arena& arena);

VirtualInterfaceBase ResolveVirtualInterfaceBaseExpr(const Expr* base,
                                                     SimContext& ctx,
                                                     Arena& arena);

VirtualInterfaceBase ResolveVirtualInterfaceInnerPath(const Expr* expr,
                                                      SimContext& ctx,
                                                      Arena& arena,
                                                      std::string& field);

std::string VirtualInterfaceComponentName(uint64_t handle,
                                          std::string_view field,
                                          const SimContext& ctx);

uint64_t VirtualInterfaceOperandHandle(const Expr* operand, SimContext& ctx,
                                       Arena& arena);

bool TryInterfaceInstancePathHandle(const Expr* expr, SimContext& ctx,
                                    Arena& arena, Logic4Vec& out);

void ReportNullVirtualInterface(SourceLoc loc, SimContext& ctx);

}  // namespace delta
