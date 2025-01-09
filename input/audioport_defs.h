#ifndef audioport_defs_h
#define audioport_defs_h

// Design parameters

//////////////////////////////////////////////////////////////////
// 1. Project parameters
//////////////////////////////////////////////////////////////////

#define student_number      "123456"
#define CLK_PERIOD          0.0
#define MCLK_PERIOD         54.25347222
#define FILTER_TAPS         0
#define AUDIO_FIFO_SIZE     0

//////////////////////////////////////////////////////////////////
// 2. Register counts for address computation
//////////////////////////////////////////////////////////////////

#define DSP_REGISTERS       0
#define AUDIOPORT_REGISTERS 0

//////////////////////////////////////////////////////////////////
// 3. Register indicec
//////////////////////////////////////////////////////////////////

#define CMD_REG_INDEX         0
#define STATUS_REG_INDEX      0
#define LEVEL_REG_INDEX       0
#define CFG_REG_INDEX         0
#define DSP_REGS_START_INDEX  0
#define DSP_REGS_END_INDEX    0
#define LEFT_FIFO_INDEX       0
#define RIGHT_FIFO_INDEX      0

//////////////////////////////////////////////////////////////////
// 4. Register addresses in APB address spaces
//////////////////////////////////////////////////////////////////   

#define AUDIOPORT_START_ADDRESS  0x8c000000   
#define AUDIOPORT_END_ADDRESS    0x8c000000   
#define CMD_REG_ADDRESS          0x8c000000   
#define STATUS_REG_ADDRESS       0x8c000000   
#define LEVEL_REG_ADDRESS        0x8c000000   
#define CFG_REG_ADDRESS          0x8c000000   
#define DSP_REGS_START_ADDRESS   0x8c000000   
#define DSP_REGS_END_ADDRESS     0x8c000000   
#define LEFT_FIFO_ADDRESS        0x8c000000   
#define RIGHT_FIFO_ADDRESS       0x8c000000   

//////////////////////////////////////////////////////////////////
// 5. Useful Constants
//////////////////////////////////////////////////////////////////   

// a: Command register CMD_REG

#define CMD_NOP          0x0
#define CMD_CLR          0x1
#define CMD_CFG          0x2
#define CMD_START        0x4
#define CMD_STOP         0x8
#define CMD_LEVEL        0x10   
#define CMD_IRQACK       0x20   

// b: Status register STATUS_REG

#define STATUS_PLAY      0
#define STATUS_NODATA    1

// c: Configuration register CFG_REG   

// Config bit indices
#define CFG_FILTER      0

// Config bit values
#define DSP_FILTER_OFF  0
#define DSP_FILTER_ON   1

// d: Constants used in dsp_unit

#define DATABITS      24
#define COEFFBITS     32

// e: These are needed in the testbench

#define CLK_DIV_48000        (ceil((1000000000.0/48000.0)/(CLK_PERIOD)))

// g: dsp_unit max latency

#define DSP_UNIT_MAX_LATENCY  (ceil(double(CLK_DIV_48000)/16.0))

#endif
