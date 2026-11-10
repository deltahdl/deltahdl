#include <gtest/gtest.h>

#include <array>
#include <cstdint>
#include <string>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ScopeAndLifetimeSimulation, ExplicitStaticInAutoFuncBlockPersists) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  function automatic int get_id();\n"
      "    begin\n"
      "      static int next_id = 0;\n"
      "      next_id = next_id + 1;\n"
      "      return next_id;\n"
      "    end\n"
      "  endfunction\n"
      "  initial begin\n"
      "    result = get_id();\n"
      "    result = get_id();\n"
      "    result = get_id();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 3u);
}

TEST(ScopeAndLifetimeSimulation, ExplicitAutoInStaticFuncBlockFresh) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  function static int get_val();\n"
      "    begin\n"
      "      automatic int temp = 10;\n"
      "      temp = temp + 1;\n"
      "      return temp;\n"
      "    end\n"
      "  endfunction\n"
      "  initial begin\n"
      "    result = get_val();\n"
      "    result = get_val();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 11u);
}

TEST(ScopeAndLifetimeSimulation, ForLoopVarHasLocalScope) {
  auto val = RunAndGet(
      "module t;\n"
      "  int x;\n"
      "  initial begin\n"
      "    x = 100;\n"
      "    for (int x = 0; x < 5; x = x + 1) begin\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 100u);
}

TEST(ScopeAndLifetimeSimulation, StaticFunctionVarsPersist) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  function static int counter();\n"
      "    int cnt;\n"
      "    cnt = cnt + 1;\n"
      "    return cnt;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    result = counter();\n"
      "    result = counter();\n"
      "    result = counter();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 3u);
}

TEST(ScopeAndLifetimeSimulation, AutomaticFunctionVarsFresh) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  function automatic int counter();\n"
      "    int cnt;\n"
      "    cnt = cnt + 1;\n"
      "    return cnt;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    result = counter();\n"
      "    result = counter();\n"
      "    result = counter();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 1u);
}

TEST(ScopeAndLifetimeSimulation, DefaultFunctionIsStatic) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  function int counter();\n"
      "    int cnt;\n"
      "    cnt = cnt + 1;\n"
      "    return cnt;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    result = counter();\n"
      "    result = counter();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 2u);
}

TEST(ScopeAndLifetimeSimulation, DefaultLifetimeInAutoModuleIsAutomatic) {
  auto val = RunAndGet(
      "module automatic t;\n"
      "  logic [31:0] result;\n"
      "  function int counter();\n"
      "    int cnt;\n"
      "    cnt = cnt + 1;\n"
      "    return cnt;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    result = counter();\n"
      "    result = counter();\n"
      "    result = counter();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 1u);
}

TEST(ScopeAndLifetimeSimulation, UnnamedBlockVarVisibleToNestedBlock) {
  auto val = RunAndGet(
      "module t;\n"
      "  int observed;\n"
      "  initial begin\n"
      "    static int outer = 5;\n"
      "    begin\n"
      "      outer = outer + 10;\n"
      "    end\n"
      "    observed = outer;\n"
      "  end\n"
      "endmodule\n",
      "observed");
  EXPECT_EQ(val, 15u);
}

TEST(ScopeAndLifetimeSimulation,
     StaticLocalOfOneClassMethodIsNotAnotherClasss) {
  auto val = RunAndGet(
      "module t;\n"
      "  class A;\n"
      "    static function int bump(); static int n; n++; return n;\n"
      "    endfunction\n"
      "  endclass\n"
      "  class B;\n"
      "    static function int bump(); static int n; n++; return n;\n"
      "    endfunction\n"
      "  endclass\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    void'(A::bump());\n"
      "    void'(A::bump());\n"
      "    result = B::bump();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 1u);
}

TEST(ScopeAndLifetimeSimulation, AutomaticLoopBodyLocalInitializedEachEntry) {
  const char* src =
      "class N;\n"
      "  function int m();\n"
      "    int s = 0;\n"
      "    for (int i = 0; i < 4; i++) begin\n"
      "      int j = 0;\n"
      "      j += i;\n"
      "      s += j;\n"
      "    end\n"
      "    return s;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  function automatic int f();\n"
      "    int s = 0, i = 0;\n"
      "    while (i < 3) begin\n"
      "      int k = 1;\n"
      "      i++;\n"
      "      k *= i;\n"
      "      s += k;\n"
      "    end\n"
      "    return s;\n"
      "  endfunction\n"
      "  N n;\n"
      "  int rf, rm;\n"
      "  initial begin\n"
      "    rf = f();\n"
      "    n = new;\n"
      "    rm = n.m();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "rf"), 6u);
  EXPECT_EQ(RunAndGet(src, "rm"), 6u);
}

TEST(ScopeAndLifetimeSimulation, AnUnnamedBlocksVariableLeavesTheModulesAlone) {
  const char* src =
      "module t;\n"
      "  logic x = 1'b1;\n"
      "  logic in_s, out_s, out_a, out_u;\n"
      "  initial begin\n"
      "    begin\n"
      "      static bit x = 1'b0;\n"
      "      in_s = x;\n"
      "    end\n"
      "    out_s = x;\n"
      "    begin\n"
      "      automatic bit x = 1'b0;\n"
      "    end\n"
      "    out_a = x;\n"
      "    begin\n"
      "      bit x;\n"
      "      x = 1'b0;\n"
      "    end\n"
      "    out_u = x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "in_s"), 0u);
  EXPECT_EQ(RunAndGet(src, "out_s"), 1u);
  EXPECT_EQ(RunAndGet(src, "out_a"), 1u);
  EXPECT_EQ(RunAndGet(src, "out_u"), 1u);
}

TEST(ScopeAndLifetimeSimulation, AnUnnamedBlocksStaticVariableKeepsItsValue) {
  auto val = RunAndGet(
      "module t;\n"
      "  int r;\n"
      "  initial begin\n"
      "    repeat (3) begin\n"
      "      int acc;\n"
      "      if (r == 0) acc = 0;\n"
      "      acc++;\n"
      "      r = acc;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 3u);
}

TEST(ScopeAndLifetimeSimulation, ANamedBlocksStaticVariableExistsBeforeItRuns) {
  auto val = RunAndGet(
      "module t;\n"
      "  int r;\n"
      "  initial begin : outer\n"
      "    inner.x = 3;\n"
      "    begin : inner\n"
      "      int x;\n"
      "      r = x;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 3u);
}

TEST(ScopeAndLifetimeSimulation, ANamedForksStaticVariableExistsBeforeItRuns) {
  auto val = RunAndGet(
      "module t;\n"
      "  int r;\n"
      "  initial begin\n"
      "    fork : mod_1\n"
      "      int y;\n"
      "      mod_2.y = 5;\n"
      "    join\n"
      "    fork : mod_2\n"
      "      int y;\n"
      "      r = y;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 5u);
}

TEST(ScopeAndLifetimeSimulation, BlocksSharingALabelKeepVariablesOfTheirOwn) {
  const char* src =
      "module t;\n"
      "  int ra, rd;\n"
      "  initial begin : a\n"
      "    begin : b\n"
      "      int c;\n"
      "      c = c + 1;\n"
      "    end\n"
      "  end\n"
      "  initial begin : d\n"
      "    #1;\n"
      "    begin : b\n"
      "      int c;\n"
      "      c = c + 10;\n"
      "    end\n"
      "  end\n"
      "  initial #2 begin\n"
      "    ra = a.b.c;\n"
      "    rd = d.b.c;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ra"), 1u);
  EXPECT_EQ(RunAndGet(src, "rd"), 10u);
}

TEST(ScopeAndLifetimeSimulation, ABlocksClassHandleKeepsItsObjectAcrossPasses) {
  auto val = RunAndGet(
      "module t;\n"
      "  class C; int v; endclass\n"
      "  int r;\n"
      "  initial begin\n"
      "    repeat (2) begin : blk\n"
      "      C h;\n"
      "      if (h == null) begin h = new; h.v = 5; r = 0; end\n"
      "      else r = h.v;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 5u);
}

TEST(ScopeAndLifetimeSimulation, ANamedBlocksClassHandleExistsBeforeItRuns) {
  auto val = RunAndGet(
      "module t;\n"
      "  class C; int v; endclass\n"
      "  C k;\n"
      "  int r;\n"
      "  initial begin k = new; k.v = 7; inner.h = k; end\n"
      "  initial begin\n"
      "    #1;\n"
      "    begin : inner\n"
      "      C h;\n"
      "      r = (h == null) ? 99 : h.v;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 7u);
}

TEST(ScopeAndLifetimeSimulation, ANamedBlocksClassHandleIsReachedByItsPath) {
  auto val = RunAndGet(
      "module t;\n"
      "  class C; int v; endclass\n"
      "  int r;\n"
      "  initial begin\n"
      "    begin : inner C h; h = new; h.v = 4; end\n"
      "    #1 r = inner.h.v;\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 4u);
}

struct BlockPlace {
  const char* name;
  const char* head;
  const char* mid;
  const char* tail;
};

std::string InModule(const BlockPlace& place, const std::string& decls,
                     const std::string& body) {
  return std::string("module t;\n  int pass;\n  bit [4:0] r;\n") + place.head +
         decls + place.mid + body + place.tail + "endmodule\n";
}

std::string AggregateDecls(const std::string& lifetime) {
  return "      " + lifetime + "int arr [3];\n      " + lifetime +
         "int m [2][3];\n      " + lifetime + "int q [$];\n      " + lifetime +
         "int aa [int];\n";
}

constexpr std::array<const char*, 2> kLifetimes = {"", "automatic "};

constexpr const char* kFill =
    "      arr[2] = 5; m[1][2] = 3; q.push_back(7); aa[4] = 9;\n";

constexpr std::array kBlocksEnteredOnce = {
    BlockPlace{"named begin block", "  initial begin\n    begin : nb\n", "",
               "    end\n  end\n"},
    BlockPlace{"named fork block", "  initial begin\n    fork : nf\n",
               "      begin\n", "      end\n    join\n  end\n"},
    BlockPlace{"unnamed begin block", "  initial begin\n    begin\n", "",
               "    end\n  end\n"},
};

TEST(ScopeAndLifetimeSimulation, ABlocksAggregatesKeepTheirShape) {
  const std::string kBody =
      std::string(kFill) +
      "      r = {$size(arr) == 3 && arr[2] == 5, $size(m) == 2 && "
      "$size(m, 2) == 3 && m[1][2] == 3, q.size() == 1 && q[0] == 7, "
      "aa.num() == 1 && aa[4] == 9, 1'b1};\n";
  for (const char* lifetime : kLifetimes) {
    for (const BlockPlace& place : kBlocksEnteredOnce) {
      SCOPED_TRACE(place.name);
      const std::string kSrc = InModule(place, AggregateDecls(lifetime), kBody);
      SCOPED_TRACE(kSrc);
      EXPECT_EQ(RunAndGet(kSrc, "r"), 0x1Fu);
    }
  }
}

constexpr std::array kBlocksEnteredTwice = {
    BlockPlace{"repeated named begin block",
               "  initial repeat (2) begin : nb\n", "", "  end\n"},
    BlockPlace{"repeated unnamed begin block", "  initial repeat (2) begin\n",
               "", "  end\n"},
    BlockPlace{"repeated named fork block", "  initial repeat (2) fork : nf\n",
               "      begin\n", "      end\n  join\n"},
    BlockPlace{"named begin block of a static task",
               "  task tk();\n    begin : nb\n", "",
               "    end\n  endtask\n  initial begin tk(); tk(); end\n"},
    BlockPlace{"named begin block of a task declared static",
               "  task static tk();\n    begin : nb\n", "",
               "    end\n  endtask\n  initial begin tk(); tk(); end\n"},
    BlockPlace{"named begin block of a task with a delay",
               "  task tk();\n    #1;\n    begin : nb\n", "",
               "    end\n  endtask\n  initial begin tk(); tk(); end\n"},
    BlockPlace{"unnamed begin block of a static task",
               "  task tk();\n    begin\n", "",
               "    end\n  endtask\n  initial begin tk(); tk(); end\n"},
};

TEST(ScopeAndLifetimeSimulation, ABlocksStaticAggregatesOutliveIt) {
  const std::string kStaticHolds =
      "      if (pass == 2) r = {$size(arr) == 3 && arr[2] == 5, $size(m, 2) "
      "== 3 && m[1][2] == 3, q.size() == 1 && q[0] == 7, aa.num() == 1 && "
      "aa[4] == 9, 1'b1};\n";
  const std::string kAutomaticHolds =
      "      if (pass == 2) r = {$size(arr) == 3 && arr[2] == 0, $size(m, 2) "
      "== 3 && m[1][2] == 0, q.size() == 0, aa.num() == 0, 1'b1};\n";
  for (const BlockPlace& place : kBlocksEnteredTwice) {
    SCOPED_TRACE(place.name);
    const std::string kStatic = InModule(
        place, AggregateDecls(""), "      pass++;\n" + kStaticHolds + kFill);
    SCOPED_TRACE(kStatic);
    EXPECT_EQ(RunAndGet(kStatic, "r"), 0x1Fu);
    const std::string kAutomatic =
        InModule(place, AggregateDecls("automatic "),
                 "      pass++;\n" + kAutomaticHolds + kFill);
    SCOPED_TRACE(kAutomatic);
    EXPECT_EQ(RunAndGet(kAutomatic, "r"), 0x1Fu);
  }
}

TEST(ScopeAndLifetimeSimulation, EachGenerateInstanceKeepsItsBlocksAggregates) {
  auto val = RunAndGet(
      "module t;\n"
      "  bit [1:0] r;\n"
      "  for (genvar g = 0; g < 2; g++) begin : gb\n"
      "    initial repeat (2) begin : nb\n"
      "      int q [$];\n"
      "      if (q.size() == 1) r[g] = q[0] == g;\n"
      "      q.push_back(g);\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 3u);
}

TEST(ScopeAndLifetimeSimulation, AnAutomaticTasksBlockAggregatesStartAfresh) {
  constexpr std::array<const char*, 2> kDelays = {"", "    #1;\n"};
  for (const char* delay : kDelays) {
    const std::string kSrc =
        std::string(
            "module t;\n"
            "  int pass;\n"
            "  bit [3:0] r;\n"
            "  task automatic tk();\n") +
        delay +
        "    begin : nb\n"
        "      int arr [3];\n"
        "      int q [$];\n"
        "      int aa [int];\n"
        "      static int sq [$];\n"
        "      pass++;\n"
        "      if (pass == 2) r = {$size(arr) == 3 && arr[2] == 0, q.size() == "
        "0, aa.num() == 0, sq.size() == 1};\n"
        "      arr[2] = 5; q.push_back(7); aa[4] = 9; sq.push_back(1);\n"
        "    end\n"
        "  endtask\n"
        "  initial begin tk(); tk(); end\n"
        "endmodule\n";
    SCOPED_TRACE(kSrc);
    EXPECT_EQ(RunAndGet(kSrc, "r"), 0xFu);
  }
}

TEST(ScopeAndLifetimeSimulation, AStaticFunctionsBlockAggregatesOutliveIt) {
  auto val = RunAndGet(
      "module t;\n"
      "  int pass;\n"
      "  bit [3:0] r;\n"
      "  function void f();\n"
      "    begin : nb\n"
      "      int arr [3];\n"
      "      int q [$];\n"
      "      int aa [int];\n"
      "      int n;\n"
      "      pass++;\n"
      "      if (pass == 2) r = {$size(arr) == 3 && arr[2] == 5, q.size() == 1 "
      "&& q[0] == 7, aa.num() == 1 && aa[4] == 9, n == 1};\n"
      "      arr[2] = 5; q.push_back(7); aa[4] = 9; n++;\n"
      "    end\n"
      "  endfunction\n"
      "  initial begin f(); f(); end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 0xFu);
}

TEST(ScopeAndLifetimeSimulation, TwoBlocksOfATaskKeepQueuesOfTheirOwn) {
  auto val = RunAndGet(
      "module t;\n"
      "  int pass;\n"
      "  bit [1:0] r;\n"
      "  task tk();\n"
      "    pass++;\n"
      "    begin : b1\n"
      "      int q [$];\n"
      "      q.push_back(1);\n"
      "      if (pass == 2) r[0] = q.size() == 2 && q[1] == 1;\n"
      "    end\n"
      "    begin : b2\n"
      "      int q [$];\n"
      "      q.push_back(2);\n"
      "      if (pass == 2) r[1] = q.size() == 2 && q[1] == 2;\n"
      "    end\n"
      "  endtask\n"
      "  initial begin tk(); tk(); end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 3u);
}

TEST(ScopeAndLifetimeSimulation, ABlocksInitializedStaticIsInitializedOnce) {
  auto val = RunAndGet(
      "module t;\n"
      "  int pass;\n"
      "  bit [3:0] r;\n"
      "  task tk();\n"
      "    begin : nb\n"
      "      static int x = 10;\n"
      "      pass++;\n"
      "      r[pass - 1] = x == 9 + pass;\n"
      "      x++;\n"
      "    end\n"
      "  endtask\n"
      "  function void f();\n"
      "    begin : fb\n"
      "      static int y = 10;\n"
      "      r[pass + 1] = y == 9 + pass;\n"
      "      y++;\n"
      "    end\n"
      "  endfunction\n"
      "  initial begin tk(); f(); tk(); f(); end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 0xFu);
}

std::string BlockAggregateFunction(const char* qualifier) {
  return std::string("  ") + qualifier +
         "function bit [4:0] f();\n"
         "    bit [4:0] res;\n"
         "    begin : nb\n"
         "      int arr [3];\n"
         "      int q [$];\n"
         "      int aa [int];\n"
         "      int n;\n"
         "      static int sq [$];\n"
         "      res = {arr[2] == 5, q.size() == 1, aa.num() == 1, n == 1, "
         "sq.size() == 1};\n"
         "      arr[2] = 5; q.push_back(7); aa[4] = 9; n++; sq.push_back(1);\n"
         "    end\n"
         "    return res;\n"
         "  endfunction\n";
}

TEST(ScopeAndLifetimeSimulation,
     ABlocksAggregatesKeepTheirSubroutinesLifetime) {
  struct Place {
    std::string src;
    uint64_t want;
  };
  const std::string kFn = BlockAggregateFunction("");
  const std::array<Place, 10> kPlaces = {{
      {"package p;\n" + kFn +
           "endpackage\n"
           "module t;\n"
           "  bit [4:0] r;\n"
           "  initial begin void'(p::f()); r = p::f(); end\n"
           "endmodule\n",
       0x1F},
      {"interface ifc;\n" + kFn +
           "endinterface\n"
           "module t;\n"
           "  bit [4:0] r;\n"
           "  ifc i();\n"
           "  initial begin void'(i.f()); r = i.f(); end\n"
           "endmodule\n",
       0x1F},
      {"module t;\n"
       "  bit [4:0] r;\n"
       "  program pg;\n" +
           kFn +
           "    initial begin void'(f()); r = f(); end\n"
           "  endprogram\n"
           "endmodule\n",
       0x1F},
      {"module t;\n"
       "  bit [4:0] r;\n"
       "  if (1) begin : g\n" +
           kFn +
           "  end\n"
           "  initial begin void'(g.f()); r = g.f(); end\n"
           "endmodule\n",
       0x1F},
      {kFn + "module t;\n"
             "  bit [4:0] r;\n"
             "  initial begin void'(f()); r = f(); end\n"
             "endmodule\n",
       0x1F},
      {"module t;\n"
       "  bit [4:0] r;\n"
       "  for (genvar i = 0; i < 2; i++) begin : g\n" +
           kFn +
           "  end\n"
           "  initial begin void'(g[1].f()); r = g[1].f(); end\n"
           "endmodule\n",
       0x1F},
      {"module t;\n"
       "  bit [4:0] r;\n"
       "  case (1)\n"
       "    1: begin : g\n" +
           kFn +
           "    end\n"
           "  endcase\n"
           "  initial begin void'(g.f()); r = g.f(); end\n"
           "endmodule\n",
       0x1F},
      {"module t;\n"
       "  bit [4:0] r;\n"
       "  if (0) begin : h end\n"
       "  else begin : g\n" +
           kFn +
           "  end\n"
           "  initial begin void'(g.f()); r = g.f(); end\n"
           "endmodule\n",
       0x1F},
      {"module automatic t;\n"
       "  bit [4:0] r;\n"
       "  if (1) begin : g\n" +
           kFn +
           "  end\n"
           "  initial begin void'(g.f()); r = g.f(); end\n"
           "endmodule\n",
       0x01},
      {"class C;\n" + BlockAggregateFunction("static ") +
           "endclass\n"
           "module t;\n"
           "  bit [4:0] r;\n"
           "  initial begin void'(C::f()); r = C::f(); end\n"
           "endmodule\n",
       0x01},
  }};
  for (const Place& place : kPlaces) {
    SCOPED_TRACE(place.src);
    EXPECT_EQ(RunAndGet(place.src, "r"), place.want);
  }
}

}  // namespace
