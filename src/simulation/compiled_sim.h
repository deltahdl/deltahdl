#pragma once

#include <cstdint>
#include <functional>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "parser/ast.h"

namespace delta {

class SimContext;

// =============================================================================
// CompiledProcess: a pre-compiled fast path for simple processes
// =============================================================================

class CompiledProcess {
 public:
  using CompiledFn = std::function<void(SimContext&)>;

  CompiledProcess(uint32_t id, CompiledFn fn);

  uint32_t Id() const { return id_; }
  void Execute(SimContext& ctx) const;
  bool IsValid() const { return fn_ != nullptr; }

 private:
  uint32_t id_;
  CompiledFn fn_;
};

// =============================================================================
// ProcessCompiler: analyzes a process and generates a compiled version
// =============================================================================

class ProcessCompiler {
 public:
  /// Returns true if the statement tree is eligible for compilation.
  /// Only pure combinational processes (no timing controls) qualify.
  static bool IsCompilable(const Stmt* body);

  /// Attempt to compile a process. Returns a CompiledProcess with a null
  /// function if compilation is not possible.
  static CompiledProcess Compile(uint32_t id, const Stmt* body);

 private:
  static bool HasTimingControl(const Stmt* stmt);
  static bool HasTimingControlInBlock(const std::vector<Stmt*>& stmts);
};

}  // namespace delta
