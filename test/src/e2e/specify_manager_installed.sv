module specify_manager_installed(input a, output y);
  specify
    (a => y) = 5;
  endspecify

  initial
$sdf_annotate("test/src/e2e/specify_manager_installed_missing.sdf");
endmodule
