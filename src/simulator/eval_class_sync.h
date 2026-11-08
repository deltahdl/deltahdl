#pragma once

#include <cstdint>
#include <string>
#include <string_view>

#include "common/source_loc.h"

namespace delta {

struct ClassMember;
struct ClassObject;
struct ClassTypeInfo;
struct DataType;
struct Expr;
struct Logic4Vec;
struct MailboxObject;
struct SemaphoreObject;
struct Stmt;
struct Variable;
class Arena;
class SimContext;

enum class SyncKind : uint8_t { kNone, kSemaphore, kMailbox };

SyncKind BuiltinSyncKindOf(std::string_view name, const SimContext& ctx);

SyncKind SyncKindOfType(const DataType& type, std::string_view package,
                        const SimContext& ctx);
SyncKind SyncKindOfType(const DataType& type, const SimContext& ctx);

struct SyncProperty {
  SyncKind kind = SyncKind::kNone;
  ClassObject* obj = nullptr;
  const ClassMember* member = nullptr;
  const ClassTypeInfo* declaring = nullptr;
  std::string spelling;
};

SyncProperty ResolveSyncProperty(const Expr* recv, SimContext& ctx,
                                 Arena& arena);

SemaphoreObject* SemaphoreOfProperty(const SyncProperty& prop,
                                     std::string_view method, SourceLoc loc,
                                     SimContext& ctx);
MailboxObject* MailboxOfProperty(const SyncProperty& prop,
                                 std::string_view method, SourceLoc loc,
                                 SimContext& ctx);

void BuildSyncProperty(const SyncProperty& prop, const Expr* new_expr,
                       SimContext& ctx, Arena& arena);

bool TryInitClassSyncProperty(ClassObject* obj, const ClassTypeInfo* info,
                              std::string_view name, const Expr* init,
                              SimContext& ctx);

bool TryInitStaticSyncProperty(const ClassTypeInfo* info, std::string_view name,
                               const Expr* init, SimContext& ctx);

bool TrySyncHandleAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

struct SyncHandle {
  SyncKind kind = SyncKind::kNone;
  SemaphoreObject* sem = nullptr;
  MailboxObject* mbx = nullptr;
};

SyncHandle ResolveSyncActual(SyncKind kind, const Expr* actual, SimContext& ctx,
                             Arena& arena);

void BindSyncFormal(const SyncHandle& actual, Variable* var, SimContext& ctx);

SemaphoreObject* SemaphoreOfFormal(const Expr* recv, SimContext& ctx);
MailboxObject* MailboxOfFormal(const Expr* recv, SimContext& ctx);

void BuildBuiltinSyncBase(ClassObject* obj, std::string_view base_class,
                          const Expr* super_new, SimContext& ctx, Arena& arena);

SemaphoreObject* BuiltinBaseSemaphore(const Expr* expr, std::string_view method,
                                      SimContext& ctx, Arena& arena);
MailboxObject* BuiltinBaseMailbox(const Expr* expr, std::string_view method,
                                  SimContext& ctx, Arena& arena);

Logic4Vec NewContainedSyncObject(const Expr* new_expr,
                                 std::string_view class_type, SimContext& ctx,
                                 Arena& arena);
void RecordContainedSyncHandle(const Expr* item, SimContext& ctx, Arena& arena);
SemaphoreObject* ContainedSemaphoreOf(const Expr* elem, SimContext& ctx,
                                      Arena& arena);
MailboxObject* ContainedMailboxOf(const Expr* elem, SimContext& ctx,
                                  Arena& arena);

}  // namespace delta
