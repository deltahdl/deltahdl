// §32.9's $sdf_annotate is what makes the SpecifyManager a run installs
// visible from outside the process. EvalSdfAnnotateTask in
// src/simulator/sdf_annotate_task.cpp returns at once and prints nothing when
// SimContext::GetSpecifyManager is null, so a run that installs no manager
// prints nothing at all for this design. With a manager installed the call
// reaches RunSdfAnnotateTask in the same file, which cannot read the named SDF
// file and returns the warning recorded below.
//
// The named SDF file does not exist and nothing creates it.
//
// §30.4.1 restricts a module path source to an input or inout port and its
// destination to an output or inout port, so the module declares the two ports
// its module path joins. The specify block is in the top module because a run
// registers the specify blocks of its top modules alone.
module specify_manager_installed(input a, output y);
  specify
    (a => y) = 5;
  endspecify

  // The call stands at column 1 so that the caret line printed beneath the
  // reported source line is exactly two spaces and a caret:
  // src/common/diagnostic.cpp writes "  ", then column - 1 spaces, then "^".
  // Every other byte of specify_manager_installed.expected follows from
  // reading the sources.
  initial
$sdf_annotate("test/src/e2e/specify_manager_installed_missing.sdf");
endmodule
