#include <gtest/gtest.h>

#include <cstdint>
#include <utility>
#include <vector>

#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

// Annex H.9 defines the DPI-C context call chain: a sequence of C subroutine
// invocations that starts with a SystemVerilog entity calling a DPI-C import
// declared with the context keyword and continues in C, unbroken by a call
// back into SystemVerilog; imported calls are not instrumented unless the
// import is declared context, and the behavior of the DPI utility functions
// that manipulate context is undefined outside a context chain. The cases
// check when the runtime is in a chain and whether that chain is a context
// one, that an export call -- a call back into SystemVerilog -- ends the
// chain so that an import the export's code calls starts a chain of its own,
// resumed when the export returns, and that the context property is the
// innermost import's rather than promoted from the chain's root.

namespace {

// A runtime holding a context import `ctx_import`, a noncontext import
// `plain_import`, both in the scope top, and an export `sv_exp` in that
// scope whose body is the one given.
DpiRuntime RuntimeWithExport(DpiRtCallback export_body) {
  DpiRuntime rt;
  DpiRtFunction ctx;
  ctx.c_name = "c_ctx";
  ctx.sv_name = "ctx_import";
  ctx.is_context = true;
  ctx.impl = [](const std::vector<DpiArgValue>&) {
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(ctx);
  DpiRtFunction plain;
  plain.c_name = "c_plain";
  plain.sv_name = "plain_import";
  plain.impl = [](const std::vector<DpiArgValue>&) {
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(plain);
  DpiRtExport exported;
  exported.c_name = "c_exp";
  exported.sv_name = "sv_exp";
  exported.scope_name = "top";
  exported.impl = std::move(export_body);
  rt.RegisterExport(exported);
  return rt;
}

DpiScope Top() {
  DpiScope scope;
  scope.name = "top";
  return scope;
}

// §H.9: no chain is open until SystemVerilog calls an import; a call of a
// context import opens a context chain, which closes when the call returns.
TEST(DpiContextCallChain, AChainStartsWhenSystemVerilogCallsAnImport) {
  DpiRuntime rt = RuntimeWithExport(nullptr);
  EXPECT_FALSE(rt.InCallChain());
  EXPECT_FALSE(rt.InContextCallChain());
  EXPECT_EQ(rt.OpenCallChainCount(), 0u);
  rt.EnterDeclaredImportCall("ctx_import", Top());
  EXPECT_TRUE(rt.InCallChain());
  EXPECT_TRUE(rt.InContextCallChain());
  EXPECT_EQ(rt.OpenCallChainCount(), 1u);
  rt.LeaveImportCall();
  EXPECT_FALSE(rt.InCallChain());
  EXPECT_EQ(rt.OpenCallChainCount(), 0u);
}

// §H.9: a chain that starts with an import not declared context is a chain,
// but not a context chain.
TEST(DpiContextCallChain, ANoncontextImportOpensNoContextChain) {
  DpiRuntime rt = RuntimeWithExport(nullptr);
  rt.EnterDeclaredImportCall("plain_import", Top());
  EXPECT_TRUE(rt.InCallChain());
  EXPECT_FALSE(rt.InContextCallChain());
  rt.LeaveImportCall();
}

// What the export body observes: in SystemVerilog code, before it calls an
// import; and inside the import it calls.
struct Observed {
  bool in_chain_before = true;
  uint32_t open_before = 0;
  bool in_chain_inside = false;
  bool context_inside = true;
  uint32_t open_inside = 0;
};

// §H.9: the chain continues in C unbroken by a call back into SystemVerilog,
// which is where an export call takes it: inside the export, before its code
// calls an import, no chain is open at that point, the one that called the
// export standing broken off; an import the export's code calls starts a
// second chain, open beside the first and not a context chain where that
// import is not context; and when the export returns the first chain resumes
// as the context chain it was.
TEST(DpiContextCallChain, AnExportCallEndsTheChainAndItsImportsStartAnother) {
  Observed observed;
  DpiRuntime* runtime = nullptr;
  DpiRuntime rt =
      RuntimeWithExport([&observed, &runtime](const std::vector<DpiArgValue>&) {
        observed.in_chain_before = runtime->InCallChain();
        observed.open_before = runtime->OpenCallChainCount();
        runtime->EnterDeclaredImportCall("plain_import", Top());
        observed.in_chain_inside = runtime->InCallChain();
        observed.context_inside = runtime->InContextCallChain();
        observed.open_inside = runtime->OpenCallChainCount();
        runtime->LeaveImportCall();
        return DpiArgValue::FromInt(0);
      });
  runtime = &rt;
  rt.EnterDeclaredImportCall("ctx_import", Top());
  DpiArgValue result;
  EXPECT_EQ(rt.CallExportFromImport("sv_exp", {}, &result),
            DpiExportCallStatus::kOk);
  EXPECT_FALSE(observed.in_chain_before);
  EXPECT_EQ(observed.open_before, 1u);
  EXPECT_TRUE(observed.in_chain_inside);
  EXPECT_FALSE(observed.context_inside);
  EXPECT_EQ(observed.open_inside, 2u);
  EXPECT_TRUE(rt.InCallChain());
  EXPECT_TRUE(rt.InContextCallChain());
  EXPECT_EQ(rt.OpenCallChainCount(), 1u);
  rt.LeaveImportCall();
}

// §H.9 with §35.5.3: within one chain the context property is the innermost
// import's, not promoted from the root: a noncontext import called from C
// inside a context chain leaves the chain open but not a context chain until
// it returns.
TEST(DpiContextCallChain, TheContextPropertyIsTheInnermostImports) {
  DpiRuntime rt = RuntimeWithExport(nullptr);
  rt.EnterDeclaredImportCall("ctx_import", Top());
  rt.EnterDeclaredImportCall("plain_import", Top());
  EXPECT_TRUE(rt.InCallChain());
  EXPECT_FALSE(rt.InContextCallChain());
  EXPECT_EQ(rt.OpenCallChainCount(), 1u);
  rt.LeaveImportCall();
  EXPECT_TRUE(rt.InContextCallChain());
  rt.LeaveImportCall();
}

}  // namespace
