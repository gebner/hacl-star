def('LOWSTARSAMPLE', [
    {filename: 'code/bignum/Hacl.Bignum.Addition.fst'},
    {filename: 'code/bignum/Hacl.Bignum.Lib.fst'},
])
def('PULSESAMPLE', [
    {filename: 'code/bignum/Hacl.Bignum.AdditionPulse.fst'},
    {filename: 'code/bignum/Hacl.Bignum.LibPulse.fst'},
])
def('LOWSTAR', env.files)

$`You are an expert in formal verification,
working on porting the HACL library from Low* to Pulse.

You have already successfully ported some files:
LOWSTARSAMPLE to PULSESAMPLE

You are now porting LOWSTAR.  Please write the Pulse version of this file.`