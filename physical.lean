/-
Physical spaces based on affine spaces
-/

import  .affine_space

open affine_space

inductive physical_space 
| location      -- no floor
| mass          -- floor at 0
| time          -- no floor
| current       -- no floor
| temperature   -- floor at 0K   
| amount        -- floor at 0 particles
| intensity     -- has floor at 0 c
open physical_space

def physical_space_id (q: physical_space) : ℕ  :=
    match q with 
    | location      := 0
    | mass          := 1
    | time          := 2
    | current       := 3
    | temperature   := 4
    | amount        := 5
    | intensity     := 6
    end

def phys_space (q : physical_space) := 
    space.mk (physical_space_id q)


-- standard affine space of geometric locations
def std_loc_space := phys_space location 
def std_loc_frame := std_frame std_loc_space
def std_loc_point := std_point std_loc_space
def std_loc_vector := std_vector std_loc_space
def mk_loc (c : scalar) := point.mk std_loc_frame c

-- standard mass objects
def std_mass_space := phys_space mass 
def std_mass_frame := std_frame std_mass_space
def std_mass_point := std_point std_mass_space
def std_mass_vector := std_vector std_mass_space
def mk_mass (c : scalar) := point.mk std_mass_frame c

-- standard time objects
def std_time_space := phys_space time 
def std_time_frame := std_frame std_time_space
def std_time_point := std_point std_time_space
def std_time_vector := std_vector std_time_space
def mk_time (c : scalar) := point.mk std_time_frame c

-- standard current objects
def std_current_space := phys_space current
def std_current_frame := std_frame std_current_space
def std_current_point := std_point std_current_space
def std_current_vector := std_vector std_current_space
def mk_current (c : scalar) := point.mk std_current_frame c

-- standard temperature objects
def std_temp_space := phys_space temperature 
def std_temp_frame := std_frame std_temp_space
def std_temp_point := std_point std_temp_space
def std_temp_vector := std_vector std_temp_space
def mk_temp (c : scalar) := point.mk std_temp_frame c

-- standard amount objects
def std_amount_space := phys_space amount
def std_amount_frame := std_frame std_amount_space
def std_amount_point := std_point std_amount_space
def std_amount_vector := std_vector std_amount_space
def mk_amount (c : scalar) := point.mk std_amount_frame c

-- standard intensity objects
def std_intensity_space := phys_space intensity
def std_intensity_frame := std_frame std_intensity_space
def std_intensity_point := std_point std_intensity_space
def std_intensity_vector := std_vector std_intensity_space
def mk_intensity (c : scalar) := point.mk std_intensity_frame c