#include "synthesis/mem_infer.h"

#include <string>
#include <unordered_map>

#include "elaboration/rtlir.h"

namespace delta {

namespace {

// Per-memory accumulation during analysis.
struct MemAccum {
  std::string name;
  uint32_t data_width = 0;
  std::vector<MemoryPort> read_ports;
  std::vector<MemoryPort> write_ports;
};

// Get the clock edge from an always_ff process sensitivity list.
Edge GetClockEdge(const RtlirProcess& proc) {
  if (proc.sensitivity.empty()) return Edge::kNone;
  return proc.sensitivity[0].edge;
}

// Look up the width of a signal in the RTLIR module.
uint32_t LookupWidth(const RtlirModule* mod, std::string_view name) {
  for (const auto& v : mod->variables) {
    if (v.name == name) return v.width;
  }
  for (const auto& p : mod->ports) {
    if (p.name == name) return p.width;
  }
  for (const auto& n : mod->nets) {
    if (n.name == name) return n.width;
  }
  return 1;
}

// Check if a select expression represents a memory access (ident[index]).
bool IsMemSelect(const Expr* expr) {
  if (!expr) return false;
  if (expr->kind != ExprKind::kSelect) return false;
  if (!expr->base || !expr->index) return false;
  return expr->base->kind == ExprKind::kIdentifier && !expr->index_end;
}

// Add a port to the accumulator for a given memory name.
void AddPort(std::unordered_map<std::string_view, MemAccum>& mems,
             const RtlirModule* mod, const Expr* select, bool is_write,
             Edge edge) {
  std::string_view mem_name = select->base->text;
  auto& acc = mems[mem_name];
  if (acc.name.empty()) {
    acc.name = std::string(mem_name);
    acc.data_width = LookupWidth(mod, mem_name);
  }

  MemoryPort port;
  port.name = std::string(mem_name);
  port.data_width = acc.data_width;
  port.is_write = is_write;
  port.clock_edge = edge;

  // Infer address width from the index expression.
  if (select->index && select->index->kind == ExprKind::kIdentifier) {
    port.addr_width = LookupWidth(mod, select->index->text);
  } else {
    port.addr_width = 1;
  }

  if (is_write) {
    acc.write_ports.push_back(port);
  } else {
    acc.read_ports.push_back(port);
  }
}

// Scan an expression RHS for memory read accesses (mem[addr]).
void ScanReadsInExpr(const Expr* expr,
                     std::unordered_map<std::string_view, MemAccum>& mems,
                     const RtlirModule* mod, Edge edge) {
  if (!expr) return;
  if (IsMemSelect(expr)) {
    AddPort(mems, mod, expr, false, edge);
    return;
  }
  // Recurse into sub-expressions.
  ScanReadsInExpr(expr->lhs, mems, mod, edge);
  ScanReadsInExpr(expr->rhs, mems, mod, edge);
  ScanReadsInExpr(expr->condition, mems, mod, edge);
  ScanReadsInExpr(expr->true_expr, mems, mod, edge);
  ScanReadsInExpr(expr->false_expr, mems, mod, edge);
  ScanReadsInExpr(expr->base, mems, mod, edge);
}

// Scan a statement for memory read and write accesses.
void ScanStmt(const Stmt* stmt,
              std::unordered_map<std::string_view, MemAccum>& mems,
              const RtlirModule* mod, Edge edge) {
  if (!stmt) return;
  switch (stmt->kind) {
    case StmtKind::kBlock:
      for (const auto* s : stmt->stmts) {
        ScanStmt(s, mems, mod, edge);
      }
      break;
    case StmtKind::kNonblockingAssign:
    case StmtKind::kBlockingAssign:
      // Check for write: mem[addr] <= data
      if (IsMemSelect(stmt->lhs)) {
        AddPort(mems, mod, stmt->lhs, true, edge);
      }
      // Check for read: data <= mem[addr]
      ScanReadsInExpr(stmt->rhs, mems, mod, edge);
      break;
    case StmtKind::kIf:
      ScanStmt(stmt->then_branch, mems, mod, edge);
      ScanStmt(stmt->else_branch, mems, mod, edge);
      break;
    case StmtKind::kCase:
      for (const auto& ci : stmt->case_items) {
        ScanStmt(ci.body, mems, mod, edge);
      }
      break;
    default:
      break;
  }
}

}  // namespace

std::vector<InferredMemory> InferMemories(const RtlirModule* mod) {
  if (!mod) return {};

  std::unordered_map<std::string_view, MemAccum> mems;

  for (const auto& proc : mod->processes) {
    if (proc.kind != RtlirProcessKind::kAlwaysFF) continue;
    Edge edge = GetClockEdge(proc);
    ScanStmt(proc.body, mems, mod, edge);
  }

  std::vector<InferredMemory> result;
  result.reserve(mems.size());
  for (auto& [name, acc] : mems) {
    InferredMemory mem;
    mem.name = acc.name;
    mem.data_width = acc.data_width;
    mem.read_ports = std::move(acc.read_ports);
    mem.write_ports = std::move(acc.write_ports);

    // Infer depth from address width of any port.
    uint32_t addr_w = 0;
    if (!mem.read_ports.empty()) {
      addr_w = mem.read_ports[0].addr_width;
    } else if (!mem.write_ports.empty()) {
      addr_w = mem.write_ports[0].addr_width;
    }
    mem.depth = (addr_w > 0) ? (1u << addr_w) : 0;

    result.push_back(std::move(mem));
  }
  return result;
}

}  // namespace delta
