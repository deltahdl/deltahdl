#pragma once

#include <string>

#include "common/packed_range.h"
#include "common/types.h"
#include "simulator/stmt_result.h"

namespace delta {

struct Expr;
struct Stmt;
struct Variable;
class SimContext;
class Arena;

StmtResult ExecBlockingAssignImpl(const Stmt* stmt, SimContext& ctx,
                                  Arena& arena);
StmtResult ExecNonblockingAssignImpl(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena);
StmtResult ExecVarDeclImpl(const Stmt* stmt, SimContext& ctx, Arena& arena);
StmtResult ExecForceOrAssignImpl(const Stmt* stmt, SimContext& ctx,
                                 Arena& arena);
StmtResult ExecReleaseOrDeassignImpl(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena);

void PerformBlockingAssign(const Expr* lhs, const Logic4Vec& rhs_val,
                           SimContext& ctx, Arena& arena);

void ScheduleNonblockingAssign(const Stmt* stmt, const Logic4Vec& rhs_val,
                               uint64_t delay_ticks, SimContext& ctx,
                               Arena& arena);

void BuildLhsName(const Expr* expr, std::string& out);
Variable* TryResolveArrayElement(const Expr* lhs, SimContext& ctx);
bool BuildCompoundLhsName(const Expr* expr, SimContext& ctx, Arena& arena,
                          std::string& name);
Variable* TryResolveCompoundElement(const Expr* lhs, SimContext& ctx,
                                    Arena& arena);
Variable* ResolveLhsVariable(const Expr* lhs, SimContext& ctx);
bool WriteStructField(const Expr* lhs, const Logic4Vec& rhs_val,
                      SimContext& ctx);
// §11.5.1: the storage bits of `var` that the select `sel` addresses, resolved
// against the declaration, since "the actual bit that is accessed by an address
// is, in part, determined by the declaration". A width of zero is the select
// that addresses no bit of the object -- an index carrying x or z, which
// §11.5.1 has "return x" when read and have "no effect on the data stored when
// written", and an index or a range wholly outside the declared bounds, which
// the same sentence covers.
//
// One index of a packed multidimensional array addresses an element rather than
// a bit (§7.4.1), and the window is that element's.
//
// Two callers ask it: the concatenation lvalue walk, which needs an element's
// own width rather than its variable's, and the continuous-assignment lowering,
// which needs the bits a select-targeted driver drives. They asked it
// separately and of the same clause, which is what the copy-paste gate found.
PartSelectBits SelectStorageBits(const Variable& var, const Expr* sel,
                                 SimContext& ctx, Arena& arena);

void WriteBitSelect(Variable* var, const Expr* lhs, const Logic4Vec& rhs_val,
                    SimContext& ctx, Arena& arena);
Logic4Vec ResizeToWidth(Logic4Vec val, uint32_t target_width, Arena& arena);
bool TryArrayBlockingAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);
bool TryAssocIndexedWrite(const Expr* lhs, const Logic4Vec& rhs_val,
                          SimContext& ctx, Arena& arena);
bool TryQueueIndexedWrite(const Expr* lhs, const Logic4Vec& rhs_val,
                          SimContext& ctx, Arena& arena);
bool TryQueueBlockingAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

// §8.4: handle a blocking assignment whose right-hand side is a `new` call and
// whose left-hand side names a variable of a class type -- the two-step form
// `P p; p = new;` by which an object is created and its handle stored. `new`
// names a construction rather than a value to be read, so an assignment of
// this shape cannot be served by evaluating the right-hand side; it is
// recognized here, the object is created, and the handle is written to the
// target. Declines (returning false) for any other assignment, including one
// to a variable with no known class type, leaving it to the ordinary paths.
bool TryClassNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

}  // namespace delta
