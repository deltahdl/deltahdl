#include <gtest/gtest.h>

#include <cstdint>
#include <cstdio>
#include <fstream>
#include <string>

#include "fixture_simulator.h"
#include "helpers_lower_run.h"

using namespace delta;

namespace {

std::string WritePersonalityFile(const std::string& tag,
                                 const std::string& data) {
  std::string path = "/tmp/deltahdl_t201603_" + tag + ".mem";
  std::ofstream ofs(path);
  ofs << data;
  ofs.close();
  return path;
}

TEST(PlaPersonality, LoadedByProceduralAssignment) {
  SimFixture f;
  uint64_t out = RunModule(f,
                           "module t;\n"
                           "  logic [1:2] in;\n"
                           "  logic [1:2] mem [1:2];\n"
                           "  logic [1:2] out;\n"
                           "  initial begin\n"
                           "    in = 2'b10;\n"
                           "    mem[1] = 2'b10;\n"
                           "    mem[2] = 2'b01;\n"
                           "    $sync$and$array(mem, in, out);\n"
                           "  end\n"
                           "endmodule\n",
                           "out");
  EXPECT_EQ(out, 2u);
}

TEST(PlaPersonality, ChangeReflectedAtNextEvaluation) {
  SimFixture f;
  uint64_t out = RunModule(f,
                           "module t;\n"
                           "  logic [1:2] in;\n"
                           "  logic [1:2] mem [1:1];\n"
                           "  logic [1:1] first;\n"
                           "  logic [1:1] out;\n"
                           "  initial begin\n"
                           "    in = 2'b10;\n"
                           "    mem[1] = 2'b11;\n"
                           "    $sync$and$array(mem, in, first);\n"
                           "    mem[1] = 2'b10;\n"
                           "    $sync$and$array(mem, in, out);\n"
                           "  end\n"
                           "endmodule\n",
                           "out");
  EXPECT_EQ(out, 1u);
}

TEST(PlaPersonality, ChangeNotReflectedBeforeNextEvaluation) {
  SimFixture f;
  uint64_t first = RunModule(f,
                             "module t;\n"
                             "  logic [1:2] in;\n"
                             "  logic [1:2] mem [1:1];\n"
                             "  logic [1:1] first;\n"
                             "  logic [1:1] out;\n"
                             "  initial begin\n"
                             "    in = 2'b10;\n"
                             "    mem[1] = 2'b11;\n"
                             "    $sync$and$array(mem, in, first);\n"
                             "    mem[1] = 2'b10;\n"
                             "    $sync$and$array(mem, in, out);\n"
                             "  end\n"
                             "endmodule\n",
                             "first");
  EXPECT_EQ(first, 0u);
}

TEST(PlaPersonality, LoadedByReadmemb) {
  SimFixture f;
  std::string path = WritePersonalityFile("readmemb", "10\n01\n");
  std::string src =
      "module t;\n"
      "  logic [1:2] in;\n"
      "  logic [1:2] mem [1:2];\n"
      "  logic [1:2] out;\n"
      "  initial begin\n"
      "    in = 2'b10;\n"
      "    $readmemb(\"" +
      path +
      "\", mem);\n"
      "    $sync$and$array(mem, in, out);\n"
      "  end\n"
      "endmodule\n";
  uint64_t out = RunModule(f, src.c_str(), "out");
  std::remove(path.c_str());
  EXPECT_EQ(out, 2u);
}

TEST(PlaPersonality, LoadedByReadmemh) {
  SimFixture f;
  std::string path = WritePersonalityFile("readmemh", "1\n2\n");
  std::string src =
      "module t;\n"
      "  logic [1:2] in;\n"
      "  logic [1:2] mem [1:2];\n"
      "  logic [1:2] out;\n"
      "  initial begin\n"
      "    in = 2'b10;\n"
      "    $readmemh(\"" +
      path +
      "\", mem);\n"
      "    $sync$or$array(mem, in, out);\n"
      "  end\n"
      "endmodule\n";
  uint64_t out = RunModule(f, src.c_str(), "out");
  std::remove(path.c_str());
  EXPECT_EQ(out, 1u);
}

}  // namespace
