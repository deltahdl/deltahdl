#include <gtest/gtest.h>

#include <array>
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
  // §6.21: a variable declared in an unnamed block is visible both to that
  // block and to any nested block below it. Here `outer` is declared in the
  // initial block and then read and written from an inner unnamed block; the
  // write must land on that same variable, so the enclosing block observes 15
  // (5 + 10), not the original 5.
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

// §6.21: a variable explicitly declared static inside an automatic function
// has a static lifetime, one copy kept between calls, and that copy is the
// function's own -- §13.4.2 has a static subroutine's items belong to the
// subroutine that declares them. Two classes each declaring a static method
// bump() with a static local n are two functions and two copies. Two calls to
// A::bump() and one to B::bump() discriminate: one copy under the name bump
// reads 3 for B's call, and a copy each reads 1.
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

// §6.21 with §6.8: a variable of an automatic subroutine is created, and its
// initializer run, on every entry to the block declaring it. In the class
// method, `int j = 0;` starts each iteration at 0, so s sums i, 6; kept from
// the iteration before, j accumulated to 0, 1, 3, 6 and s was 10. In the
// automatic function, `int k = 1;` starts at 1, so s sums 1*i, 6 again,
// where a kept k made 1, 2, 6 and 9.
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

// §6.21 with §9.3.1: a variable declared in an unnamed block is the block's
// own, visible there and in the blocks below it, and hides the module's
// variable of the same name only inside the block. A static, an automatic and
// an uninitialized declaration each write 0 to the block's x, and the
// module's x reads its 1 after each block. Declared as the module's variable
// itself, each block's write reached the module's x.
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

// §6.21: a variable a block declares without `automatic` in a static process
// is static, one variable kept from one activation of the block to the next.
// The repeat body's acc is set to 0 on the first pass alone and counts the
// passes, so r reads 3; created afresh on each entry, acc read 0 and r 1.
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

// §6.21 with §23.6: a named block's static variable is allocated before
// simulation starts, so a write through its hierarchical name before the block
// has run lands in the variable the block then reads. Made when the block
// first ran, the write found no variable and r read 0.
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

// The same for a named fork's variable, written from a sibling fork before
// the fork declaring it has begun, as §23.6's mod_1 and mod_2 example does.
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

// §6.21 with §9.3.4: two blocks labelled b, one in each of two named blocks,
// declare two static variables. Kept in one frame under the label, the second
// block's c was the first's, so d.b.c read 11 and a.b.c read 11 too.
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

// §6.21: a class handle a block declares is static as an integral variable
// is, so the object the first pass through blk made is the second pass's.
// Made afresh on each entry, the handle read null again and r stayed 0.
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

// §6.21 with §23.6: the handle a named block declares is there before the
// block runs, so the object handed to inner.h from outside is the one the
// block reads; replaced on entry, the block read null and r was 99.
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

// §9.3.4 with §23.6: the handle is reached by its hierarchical name once its
// block has run as well, so inner.h.v reads the object the block made; never
// bound under inner.h, the read found nothing and r was 0.
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

// A place a block declaring variables stands in: the source is `head`, the
// declarations, `mid`, the statements and `tail`, within a module declaring
// an int pass and a five-bit r.
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

// A fixed-size array, a two-dimensional one, a queue and an associative array,
// each declared `lifetime` (empty or `automatic `).
std::string AggregateDecls(const std::string& lifetime) {
  return "      " + lifetime + "int arr [3];\n      " + lifetime +
         "int m [2][3];\n      " + lifetime + "int q [$];\n      " + lifetime +
         "int aa [int];\n";
}

// A static declaration and an automatic one.
constexpr std::array<const char*, 2> kLifetimes = {"", "automatic "};

constexpr const char* kFill =
    "      arr[2] = 5; m[1][2] = 3; q.push_back(7); aa[4] = 9;\n";

// The blocks entered once: a named begin-end block, a named fork, whose
// declarations its branches share, and an unnamed begin-end block, all of an
// initial procedure.
constexpr std::array kBlocksEnteredOnce = {
    BlockPlace{"named begin block", "  initial begin\n    begin : nb\n", "",
               "    end\n  end\n"},
    BlockPlace{"named fork block", "  initial begin\n    fork : nf\n",
               "      begin\n", "      end\n    join\n  end\n"},
    BlockPlace{"unnamed begin block", "  initial begin\n    begin\n", "",
               "    end\n  end\n"},
};

// §6.21 with §7.4, §7.10 and §7.8: an aggregate a block declares is a variable
// of the block with the dimensions its declaration writes, there from the
// block's first statement. A named block's static variables are made before
// any procedure starts, and the shape of each was lost on the way to the block
// running: $size(arr) was 32, the array read as the int its element is.
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

// The blocks entered twice: a named and an unnamed begin-end block and a named
// fork repeated by an initial procedure, and a named and an unnamed begin-end
// block of a static task called twice.
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
    BlockPlace{"unnamed begin block of a static task",
               "  task tk();\n    begin\n", "",
               "    end\n  endtask\n  initial begin tk(); tk(); end\n"},
};

// §6.21: a block's variable is static unless declared automatic, one variable
// whose storage outlives the block, so the second entry finds the elements,
// the queue's item and the associative array's entry the first left; an
// automatic one is made afresh on each entry, its elements 0, its queue and
// associative array empty, and its shape the same. Kept between entries only
// as variables, the static aggregates lost their shape and their contents.
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

// §6.21 with §27.4: each generate block instance is a scope of its own, and
// the static queue its named block declares is its own: the second entry in
// each instance finds the one item that instance pushed. Shared, the second
// instance's block found the first's two items and r[1] stayed 0.
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

}  // namespace
