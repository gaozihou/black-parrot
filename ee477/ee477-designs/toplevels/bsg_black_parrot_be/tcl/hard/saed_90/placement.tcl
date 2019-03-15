# placement.tcl
#
# This file contains information used by icc to specify placement of
# cell groups or blocks within the floorplan of the chip. This is quite
# difficult to make it prcess independant thus this file is in the
# hardened folder.
#
#   create_bounds -name <object_name> -coordinate { {<llx> <lly>} {<urx> <ury>} } -type <type = soft,hard,exclusive> -cycle_color { hierarchy_regex }
#

# TODO: Place any placement bounds below!

create_placement_blockage -coordinate {{254.085 432.830} {297.015 1000.830}} -name placement_blockage_0 -type hard
create_placement_blockage -coordinate {{454.030 432.830} {497.015 1000.945}} -name placement_blockage_1 -type hard
create_placement_blockage -coordinate {{654.070 432.830} {697.015 1000.935}} -name placement_blockage_2 -type hard
create_placement_blockage -coordinate {{854.050 432.830} {897.015 1000.905}} -name placement_blockage_3 -type hard
create_placement_blockage -coordinate {{1054.040 432.830} {1097.015 1000.950}} -name placement_blockage_4 -type hard
create_placement_blockage -coordinate {{1253.995 432.830} {1297.015 1000.895}} -name placement_blockage_5 -type hard
create_placement_blockage -coordinate {{1454.040 432.830} {1497.015 1000.935}} -name placement_blockage_6 -type hard

create_fp_placement -timing_driven -effort high

