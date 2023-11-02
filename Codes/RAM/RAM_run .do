vlib work

vlog Slave_RAM_intf.sv RAM.sv RAM_pkg.sv RAM_SVA.sv RAM_tb.sv RAM_top.sv +define+SIM +cover

vsim -voptargs=+acc work.RAM_top -cover -sv_seed random

add wave -position insertpoint sim:/RAM_top/SR_intf/*

coverage save RAM_cv.ucdb -onexit

run -all
