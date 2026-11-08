#pragma once

#include <string>
#include <string_view>

namespace delta {

class Arena;
class SimContext;
struct Expr;
struct GenBlockSubroutineScope;
struct ModuleItem;
struct Stmt;
struct Variable;

struct SubroutineTarget {
  ModuleItem* func = nullptr;
  std::string inst_prefix;
  const GenBlockSubroutineScope* gen_block = nullptr;
};

bool IsPackageScopedCall(const Expr* call);

std::string EvaluatedHierarchicalPath(const Expr* e, SimContext& ctx,
                                      Arena& arena);

SubroutineTarget FindSubroutineTarget(const Expr* call, SimContext& ctx,
                                      Arena& arena);

const Stmt* ExternForkjoinCall(const Expr* call, SimContext& ctx, Arena& arena);

void EnterCalleeInstance(SimContext& ctx, const SubroutineTarget& target);
void LeaveCalleeInstance(SimContext& ctx);

void EnterStaticFrameOwner(SimContext& ctx, std::string_view owner);
void LeaveStaticFrameOwner(SimContext& ctx);

struct BodyStaticFrame {
  std::string_view name;
  std::string_view owner;
  bool is_method = false;
};
BodyStaticFrame StaticFrameOfBody(const ModuleItem* func, SimContext& ctx,
                                  Arena& arena);

class StaticLocalFrameScope {
 public:
  StaticLocalFrameScope(const ModuleItem* func, SimContext& ctx, Arena& arena);
  ~StaticLocalFrameScope();
  StaticLocalFrameScope(const StaticLocalFrameScope&) = delete;
  StaticLocalFrameScope& operator=(const StaticLocalFrameScope&) = delete;
  std::string_view Name() const { return name_; }

 private:
  SimContext& ctx_;
  std::string_view name_;
  bool entered_ = false;
};

void BindGenBlockConsts(const SubroutineTarget& target, SimContext& ctx,
                        Arena& arena);

std::string CallerInstancePrefix(SimContext& ctx);

void BindActualsInCaller(const ModuleItem* func, const Expr* expr,
                         SimContext& ctx, Arena& arena);
void WritebackInCaller(const ModuleItem* func, const Expr* expr,
                       SimContext& ctx, Arena& arena);
void ExecFunctionBodyInCallee(const SubroutineTarget& target, const Expr* call,
                              Variable* ret_var, SimContext& ctx, Arena& arena);

Variable* FunctionStaticLocal(const Expr* member, SimContext& ctx,
                              Arena& arena);

}  // namespace delta
