#pragma once

#include <string_view>

#include "common/types.h"

namespace delta {

struct QueueObject;
struct ClassMember;
struct ClassObject;
struct ClassTypeInfo;
struct Expr;
class SimContext;
class Arena;

QueueObject* ClassQueueProperty(ClassObject* obj, const ClassTypeInfo* from,
                                std::string_view name, SimContext& ctx);

bool IsQueuePropertyDecl(const ClassMember* member,
                         const ClassTypeInfo* declaring, SimContext& ctx);

bool InitClassQueueProperty(ClassObject* obj, const ClassTypeInfo* info,
                            std::string_view name, const Expr* init,
                            SimContext& ctx);

QueueObject* FindQueueOfName(std::string_view name, SimContext& ctx,
                             ClassObject** owner = nullptr);

QueueObject* FindQueueOfBase(const Expr* base, SimContext& ctx, Arena& arena,
                             ClassObject** owner = nullptr);

QueueObject* FindWrittenQueueOfBase(const Expr* base, SimContext& ctx,
                                    Arena& arena, ClassObject** owner);

void AnnounceQueueChange(const Expr* base, ClassObject* owner, SimContext& ctx);

bool TryEvalQueueElementMember(const Expr* expr, SimContext& ctx, Arena& arena,
                               Logic4Vec& out);

class QueuePropertyReceiver {
 public:
  QueuePropertyReceiver(const Expr* call, SimContext& ctx, Arena& arena);
  ~QueuePropertyReceiver();
  QueuePropertyReceiver(const QueuePropertyReceiver&) = delete;
  QueuePropertyReceiver& operator=(const QueuePropertyReceiver&) = delete;

  const Expr* Call() const { return call_; }

 private:
  SimContext& ctx_;
  const Expr* call_ = nullptr;
};

}  // namespace delta
