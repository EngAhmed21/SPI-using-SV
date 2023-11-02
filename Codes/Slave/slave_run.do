vlib work

vlog Slave_RAM_intf.sv slave.sv slave_pkg.sv slave_tb.sv slave_top.sv +define+SIM +cover

vsim -voptargs=+acc work.slave_top -cover -sv_seed random

add wave -position insertpoint sim:/slave_top/SR_intf/*

coverage save slave_cv.ucdb -onexit

run -all
