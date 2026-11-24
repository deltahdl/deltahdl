#pragma once

#include <string>

#include "elaborator/elaborator.h"
#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "fixture_vpi_run.h"
#include "preprocessor/preprocessor.h"
#include "simulator/vpi_user.h"

using namespace delta;

class DelayModeOfAnInstance : public VpiDesignRun {
 protected:
  int DefDelayModeOfAChildAfter(const std::string& directive) {
    auto fid = f_.mgr.AddFile("<test>", "`" + directive +
                                            "\nmodule child;\nendmodule\n"
                                            "module top;\n"
                                            "  child u();\n"
                                            "endmodule\n");
    Preprocessor pp(f_.mgr, f_.diag, {});
    auto* cu = PreprocessAndParseCu(f_, fid, pp);
    PropagateDirectivesToCu(cu, pp);
    Elaborator elab(f_.arena, f_.diag, cu);
    auto* design = elab.Elaborate("top");
    if (design == nullptr || f_.diag.HasErrors()) return vpiUndefined;
    LowerAndRun(design, f_);
    return vpi_get(vpiDefDelayMode, By("top.u"));
  }
};
