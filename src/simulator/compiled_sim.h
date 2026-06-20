#pragma once

#include <cstdint>
#include <functional>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "parser/ast.h"

namespace delta {

class SimContext;

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

class ProcessCompiler {
 public:
  static bool IsCompilable(const Stmt* body);

  static CompiledProcess Compile(uint32_t id, const Stmt* body);

 private:
  static bool HasTimingControl(const Stmt* stmt);
  static bool HasTimingControlInBlock(const std::vector<Stmt*>& stmts);
};

}  // namespace delta
