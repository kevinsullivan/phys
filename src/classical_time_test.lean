import .classical_time

noncomputable def aTimeSpace := classicalTime.mk 0

def si := measurementSystem.si_measurement_system

noncomputable def my_standard_frame := 
    classicalTimeFrame.standard aTimeSpace si

noncomputable def my_standard_frame_algebra := classicalTimeFrameAlgebra my_standard_frame 


noncomputable def my_vector : classicalTimeVector aTimeSpace :=
    classicalTimeVector.mk  1 ⟨[2],sorry⟩

noncomputable def std_vector : classicalTimeCoordinateVector aTimeSpace 
    := {f:=my_standard_frame,..my_vector}

noncomputable def my_Point : classicalTimePoint aTimeSpace :=
    classicalTimePoint.mk  1 ⟨[0],sorry⟩


noncomputable def std_point : classicalTimeCoordinatePoint aTimeSpace 
    := {f:=my_standard_frame,..my_Point}


noncomputable def my_derived_frame : classicalTimeFrame aTimeSpace :=
    classicalTimeFrame.derived aTimeSpace my_standard_frame my_Point (λone : fin 1,my_vector) si

