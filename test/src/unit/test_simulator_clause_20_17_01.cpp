#include <cstdio>
#include <filesystem>
#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §20.17.1: $system hands its string argument to the C function system(), which
// executes it as if typed at the terminal; called as a function it returns the
// system() result with data type int; with no string argument system() is
// called with the NULL string. These tests drive the simulator's $system
// handler (eval_function.cpp) and observe the returned value and the side
// effect of the executed command.

uint64_t RunAndRead(SimFixture& f, const std::string& src,
                    std::string_view var) {
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v = f.ctx.FindVariable(var);
  EXPECT_NE(v, nullptr);
  return v ? v->value.ToUint64() : 0;
}

void RunSrc(SimFixture& f, const std::string& src) {
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
}

// §20.17.1: the command is actually executed by system() as if from the
// terminal, so a failing command reports back through the function's nonzero
// return value rather than being treated as success.
TEST(SystemTask, FunctionReportsCommandFailure) {
  SimFixture f;
  uint64_t r = RunAndRead(f,
                          "module t;\n"
                          "  int r;\n"
                          "  initial r = $system(\"exit 1\");\n"
                          "endmodule\n",
                          "r");
  EXPECT_NE(r, 0u);
}

// §20.17.1: $system may be called as a task. The string argument is executed by
// system() for its side effect; here it creates a marker file that the test
// observes on disk to confirm the command ran.
TEST(SystemTask, TaskExecutesCommandFromTerminal) {
  namespace fs = std::filesystem;
  fs::path marker =
      fs::temp_directory_path() / "deltahdl_clause_20_17_01.marker";
  std::error_code ec;
  fs::remove(marker, ec);

  SimFixture f;
  RunSrc(f,
         "module t;\n"
         "  initial $system(\"touch '" +
             marker.string() +
             "'\");\n"
             "endmodule\n");

  EXPECT_TRUE(fs::exists(marker));
  fs::remove(marker, ec);
}

// §20.17.1: called with no string argument, $system invokes the C system() with
// the NULL string, which reports whether a command processor is available. On
// the host running these tests a shell is present, so the result is nonzero -
// distinguishing this from a hard-coded zero that never consults system().
TEST(SystemTask, NoArgumentInvokesSystemWithNullString) {
  SimFixture f;
  uint64_t r = RunAndRead(f,
                          "module t;\n"
                          "  int r;\n"
                          "  initial r = $system();\n"
                          "endmodule\n",
                          "r");
  EXPECT_NE(r, 0u);
}

}  // namespace
