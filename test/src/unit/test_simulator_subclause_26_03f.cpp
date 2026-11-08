#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(PackageImportSim, PackageMailboxInitializedByNewThroughTheQualifier) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  mailbox mb = new;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int a, y;\n"
                      "  initial begin\n"
                      "    p1::mb.put(7);\n"
                      "    p1::mb.put(9);\n"
                      "    p1::mb.get(a);\n"
                      "    y = a * 10 + p1::mb.num();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            71u);
}

TEST(PackageImportSim, PackageMailboxBoundReadsThePackagesOwnParameter) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  localparam int D = 1;\n"
                      "  mailbox mb = new(D);\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    y = p1::mb.try_put(3) * 10 + p1::mb.try_put(4);\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            10u);
}

TEST(PackageImportSim, PackageSubroutinesReachTheirOwnMailboxBare) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  mailbox mb = new;\n"
                      "  task send(int v);\n"
                      "    mb.put(v);\n"
                      "  endtask\n"
                      "  function int offer(int v);\n"
                      "    return mb.try_put(v);\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::send(4);\n"
                      "    y = p1::offer(5) * 10 + p1::mb.num();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            12u);
}

TEST(PackageImportSim,
     PackageMailboxDeclaredWithoutInitializerBuiltThroughTheQualifier) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  mailbox mb;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::mb = new(1);\n"
                      "    y = p1::mb.try_put(3) * 10 + p1::mb.try_put(4);\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            10u);
}

TEST(PackageImportSim, PackageSemaphoreKeyCountReadsThePackagesOwnParameter) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  localparam int K = 2;\n"
                      "  semaphore s = new(K);\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    y = p1::s.try_get(1) * 10 + p1::s.try_get(1);\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            11u);
}

static uint64_t ModuleInitializerRead(const std::string& module_items) {
  return RunAndGet(
      "package p1;\n"
      "  class B;\n"
      "    int n = 7;\n"
      "    function int get_n();\n"
      "      return n;\n"
      "    endfunction\n"
      "  endclass\n"
      "  B b = new;\n"
      "endpackage\n"
      "module top;\n" +
          module_items + "endmodule\n",
      "y");
}

TEST(PackageImportSim,
     ModuleInitializerReadsAPackageHandleThroughTheQualifier) {
  EXPECT_EQ(ModuleInitializerRead("  int y = p1::b.get_n();\n"), 7u);
}

TEST(PackageImportSim, ModuleInitializerReadsAnImportedPackageHandle) {
  EXPECT_EQ(ModuleInitializerRead("  import p1::*;\n"
                                  "  int y = b.n;\n"),
            7u);
}

TEST(PackageImportSim, ModuleInitializerReadsAUnitHandle) {
  EXPECT_EQ(RunAndGet("class B;\n"
                      "  int n = 7;\n"
                      "  function int get_n();\n"
                      "    return n;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "B ub = new;\n"
                      "module top;\n"
                      "  int y = ub.get_n();\n"
                      "endmodule\n",
                      "y"),
            7u);
}

std::string PackageHandleArrayDesign(const std::string& body) {
  return "package p;\n"
         "  class C;\n"
         "    int v = 7;\n"
         "  endclass\n"
         "  C objs[2];\n"
         "endpackage\n"
         "module t;\n"
         "  import p::*;\n"
         "  C c;\n"
         "  int i, y;\n"
         "  initial begin\n" +
         body +
         "  end\n"
         "endmodule\n";
}

TEST(PackageScopeReferenceSim, AWriteThroughAPackageArrayElementReachesIt) {
  EXPECT_EQ(RunAndGet(PackageHandleArrayDesign("    c = new;\n"
                                               "    p::objs[1] = c;\n"
                                               "    p::objs[1].v = 5;\n"
                                               "    y = c.v;\n"),
                      "y"),
            5u);
}

TEST(PackageScopeReferenceSim,
     AWriteThroughAPackageArrayElementAtAVariableIndexReachesIt) {
  EXPECT_EQ(RunAndGet(PackageHandleArrayDesign("    c = new;\n"
                                               "    i = 1;\n"
                                               "    p::objs[i] = c;\n"
                                               "    p::objs[i].v = 5;\n"
                                               "    y = c.v;\n"),
                      "y"),
            5u);
}

TEST(PackageScopeReferenceSim, AnObjectConstructedThroughAPackageArrayElement) {
  EXPECT_EQ(
      RunAndGet(PackageHandleArrayDesign("    p::objs[0] = new;\n"
                                         "    p::objs[0].v = 3;\n"
                                         "    c = p::objs[0];\n"
                                         "    y = c.v * 10 + p::objs[0].v;\n"),
                "y"),
      33u);
}

}  // namespace
