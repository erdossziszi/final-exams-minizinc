include "globals.mzn";

% =============================================================================
% 1. EREDETI BEMENETI PARAMÉTEREK (Változatlanul hagyva a .dzn kompatibilitáshoz)
% =============================================================================
int: StudentsNr;    
int: InstructorsNr; 
int: DaysNr;    
int: SlotsPerDay;   
int: AvailabilitySlotsLenght;   
int: RoomNr;    
int: ProgrammNr;    
int: DegreeNr;  
int: RolesNr;   
int: CoursesNr; 
int: LunchTsMinLen; 

set of int: Instructors = 1..InstructorsNr; 
set of int: Students = 1..StudentsNr;   
set of int: Courses = 1..CoursesNr; 
set of int: Rooms = 1..RoomNr;  
set of int: Days = 1..DaysNr;   
set of int: Roles = 1..RolesNr; 
set of int: Programms = 1..ProgrammNr;  

int: TotalTs = DaysNr * SlotsPerDay;    
int: TotalAvTs = TotalTs div AvailabilitySlotsLenght;   

array[Instructors] of set of 1..ProgrammNr: InstructorsProgramm;    
array[Instructors, 1..TotalAvTs] of 0..1: InstructorsAvailability;   

int: SessionNr = DaysNr * RoomNr;   
set of int: Sessions = 1..SessionNr;    

array[Students] of 1..ProgrammNr: StudentsProgramm; 
array[Students] of 1..DegreeNr: StudentsDegree; 
array[Students] of Instructors: StudentsSupervisorId;   
array[Students] of set of Courses: StudentsCourseIds;   

array[Courses] of set of Instructors: CoursesInstructorIds; 

array[1..(StudentsNr + SessionNr)] of {1}: reqRoom = [1 | _ in 1..(StudentsNr + SessionNr)];

array[Roles] of int: RolesDemands;  
array[int] of Roles: RolesContinuity;   
array[Programms, Roles] of set of Instructors: InstructorRolesPerProgramm;  

array[Days] of set of 1..TotalTs: LunchStarts;  

array[Students] of var 1..10: ExamLen;  % Bemeneti vizsgálati hosszak

int: SupervisorAvailable;
array[1..2] of int: OptimalLunchLenght;
array[1..2] of int: OptimalStartTs;
array[1..2] of int: OptimalFinishTs;
int: MinimizeRooms;
array[1..2,Roles] of int: RolesSoftContinuity;
int: SameDegreeInRoom;
int: Mergeability;
array[Students] of int: TheoryticalMinCard;

% =============================================================================
% 2. FOLYTONOS IDŐRE DERIVÁLT BELSŐ KONSTANSOK
% =============================================================================
float: TotalTime = float(TotalTs);
float: SlotsPerDayF = float(SlotsPerDay);

% =============================================================================
% 3. FOLYTONOS DÖNTÉSI VÁLTOZÓK
% =============================================================================
% Kezdési időpontok és intervallumok lebegőpontosként (folytonos idő)
array[Students] of var 1.0..TotalTime: StartTs; 
array[Students] of var Rooms: StudentRoomSchedule; 
array[Students, Students] of var 0..1: CollisionMX; 

array[Students, Roles] of var set of Instructors: RolesSchedule;    
array[Students] of var set of Instructors: ExaminersSchedule;   
array[Students] of var set of Instructors: InstructorSchedule;  

array[Sessions] of var 1.0..TotalTime: LunchStartTs;    
array[Sessions] of var float(LunchTsMinLen)..SlotsPerDayF: LunchLen;    
array[Sessions] of var Rooms: SessionRoomSchedule;    

% =============================================================================
% 4. SEGÉDFÜGGVÉNYEK & PREDICATE-EK
% =============================================================================

% Folytonos nap-számítás
function var int: day_func(var float: ts) =
    bool2int(ts > 0.0) + floor((ts - 1.0) / SlotsPerDayF);

% Folytonos intervallum átfedés vizsgálata
predicate overlap(var float: s1, var float: len1, var float: s2, var float: len2) =
    not (s1 + len1 <= s2 \/ s2 + len2 <= s1);

% Oktatói felcserélhetőség ellenőrzése szimmetriatöréshez
function array[Programms, Roles] of bool: check_instructor_in_roles(int: instructor_id) =
  array2d(Programms, Roles, [
    instructor_id in InstructorRolesPerProgramm[p, r] 
    | p in Programms, r in Roles
  ]); 

function set of Courses: check_instructor_courses(int: instructor_id) =
  { c | c in Courses where instructor_id in CoursesInstructorIds[c] };

% =============================================================================
% 5. SZIMMETRIATÖRÉS (HARD CONSTRAINTS)
% =============================================================================

% Hallgatói szimmetriatörés
constraint symmetry_breaking_constraint(
    forall(s1, s2 in Students where ((s1 < s2) /\ (StudentsProgramm[s1] == StudentsProgramm[s2]) /\ (StudentsCourseIds[s1] == StudentsCourseIds[s2]))) (
        StartTs[s1] <= StartTs[s2]
    )
);

% Oktatói szimmetriatörés (lex_ge használatával)
constraint symmetry_breaking_constraint(
    forall(i1, i2 in Instructors where (
        (i1 < i2) /\ 
        (check_instructor_in_roles(i1) == check_instructor_in_roles(i2)) /\
        (check_instructor_courses(i1) == check_instructor_courses(i2))
    )) (
        lex_ge([bool2int(i1 in InstructorSchedule[s]) | s in Students], 
               [bool2int(i2 in InstructorSchedule[s]) | s in Students])
    )
);

% =============================================================================
% 6. FOLYTONOS IDŐBELI ÉS KAPACITÁSI MEGKÖTÉSEK
% =============================================================================

% Ebédszünetek kezdőablaka (a diszkrét LunchStarts halmazok alapján)
constraint forall(r in Rooms, d in Days) (
    let {
        int: sess = (d - 1) * RoomNr + r;
    } in (
        LunchStartTs[sess] >= float(min(LunchStarts[d])) /\
        LunchStartTs[sess] <= float(max(LunchStarts[d]))
    )
);

% Ütközési mátrix kitöltése folytonos átfedés alapján
constraint forall(s1, s2 in Students where s1 < s2) (
    if overlap(StartTs[s1], float(ExamLen[s1]), StartTs[s2], float(ExamLen[s2])) then
        CollisionMX[s1, s2] == 1 /\ CollisionMX[s2, s1] == 1
    else
        CollisionMX[s1, s2] == 0 /\ CollisionMX[s2, s1] == 0
    endif
);

% Ebéd és Vizsga nem ütközhet ugyanabban a teremben
constraint forall(s in Students, L in Sessions) (
    if StudentRoomSchedule[s] == SessionRoomSchedule[L] then
        not overlap(StartTs[s], float(ExamLen[s]), LunchStartTs[L], LunchLen[L])
    endif
);

% Ebédek sorrendje a termekben
constraint forall(d in Days) (
    strictly_increasing([ SessionRoomSchedule[(d - 1) * RoomNr + r] | r in Rooms ])
);

% 1 exam per room: Ha két vizsga ütközik időben, nem lehetnek ugyanabban a teremben
constraint forall(i, j in Students where i < j) (
    if CollisionMX[i, j] == 1 then
        StudentRoomSchedule[i] != StudentRoomSchedule[j]
    endif
);

% A vizsga nem nyúlhat át a következő napra (folytonos naphatár tartása)
constraint forall(s in Students) (
    day_func(StartTs[s]) == day_func(StartTs[s] + float(ExamLen[s]) - 0.001)
);

% Oktatók elérhetősége (folytonos időponthoz rendelhető idősáv alapján)
constraint forall(s in Students) (
    forall(i in InstructorSchedule[s]) (
        InstructorsAvailability[i, day_func(StartTs[s])] == 1
    )
);

% =============================================================================
% 7. OKTATÓI ÉS SZEREPKÖRI FELELŐSSÉGEK (HARD CONSTRAINTS)
% =============================================================================

constraint forall(s in Students, r in Roles where RolesDemands[r] > 0) (       
    RolesSchedule[s, r] subset InstructorRolesPerProgramm[StudentsProgramm[s], r] /\
    card(RolesSchedule[s, r]) == RolesDemands[r]
);

constraint RolesNr > 1 ->
    forall(s in Students, r1, r2 in Roles where r1 < r2) (       
        disjoint(RolesSchedule[s, r1], RolesSchedule[s, r2])
    );

constraint forall(r in Roles where RolesDemands[r] == 0, s in Students) (
    card(RolesSchedule[s, r]) == 0
);

% Ebéd előtti/utáni szerepköri folytonosság
constraint length(RolesContinuity) > 0 ->
    forall(s1, s2 in Students where s1 < s2) (
        let { var int: day_s1 = day_func(StartTs[s1]); } in
        if (day_s1 == day_func(StartTs[s2])) then
            let { var int: room_s1 = StudentRoomSchedule[s1]; } in 
            if (room_s1 == StudentRoomSchedule[s2]) then
                let { var float: lunch_start = LunchStartTs[(day_s1 - 1) * RoomNr + room_s1]; } in
                if ((lunch_start > StartTs[s1]) == (lunch_start > StartTs[s2])) then 
                    forall(role in RolesContinuity) (
                        RolesSchedule[s1, role] == RolesSchedule[s2, role]
                    )
                endif
            endif
        endif
    );

% Kurzusok és Vizsgáztatók
constraint forall(s in Students where card(StudentsCourseIds[s]) == 0) (
    card(ExaminersSchedule[s]) == 0
);

constraint forall(s in Students where card(StudentsCourseIds[s]) > 0) (
    card(ExaminersSchedule[s]) <= card(StudentsCourseIds[s]) /\
    forall(c in StudentsCourseIds[s]) (
        not disjoint(CoursesInstructorIds[c], ExaminersSchedule[s])
    )
);

% Nincs párhuzamos beosztás ugyanannak az oktatónak
constraint forall(i, j in Students where i < j) (
    if CollisionMX[i, j] == 1 then
        disjoint(InstructorSchedule[i], InstructorSchedule[j])
    endif
);

% InstructorSchedule felépítése
constraint forall(s in Students) (
    array_union(row(RolesSchedule, s)) union ExaminersSchedule[s] == InstructorSchedule[s]
);

% Azonos szak egy szekcióban (nap és terem egyezése esetén)
constraint forall(s1, s2 in Students where s1 < s2)(
    if (StudentRoomSchedule[s1] == StudentRoomSchedule[s2] /\ (day_func(StartTs[s1]) == day_func(StartTs[s2]))) then
        StudentsProgramm[s1] == StudentsProgramm[s2]
    endif
);

% =============================================================================
% 8. SOFT CONSTRAINTS ÉS CÉLFÜGGVÉNY
% =============================================================================

var float: supervisor_available = if (SupervisorAvailable == 0) then 0.0 else 
    float(SupervisorAvailable) * sum(s in Students) (
       1.0 - float(InstructorsAvailability[StudentsSupervisorId[s], day_func(StartTs[s])])
    ) endif;

var float: optimal_lunch_len = if (OptimalLunchLenght[1] == 0) then 0.0 else
    float(OptimalLunchLenght[1]) * sum(L in Sessions)(abs(LunchLen[L] - float(OptimalLunchLenght[2]))) endif;

var float: optimal_start_ts = if (OptimalStartTs[1] == 0) then 0.0 else
    float(OptimalStartTs[1]) * sum(s in Students where (floor(StartTs[s] - 1.0) mod SlotsPerDay) < OptimalStartTs[2] - 1)
                           (float(OptimalStartTs[2] - 1) - (StartTs[s] - 1.0)) endif;

var float: optimal_finish_ts = if (OptimalFinishTs[1] == 0) then 0.0 else
    float(OptimalFinishTs[1]) * sum(s in Students where (floor(StartTs[s] + float(ExamLen[s]) - 2.0) mod SlotsPerDay) > OptimalFinishTs[2] - 1)
                            ((StartTs[s] + float(ExamLen[s]) - 2.0) - float(OptimalFinishTs[2] - 1)) endif;   

var float: minimize_rooms = if (MinimizeRooms == 0) then 0.0 else
    float(MinimizeRooms) * (card(array2set(StudentRoomSchedule)) - day_func(sum(s in Students)(float(ExamLen[s])))) endif;

var float: roles_soft_continuity = 
    sum(role in Roles where RolesSoftContinuity[2, role] > 0)
    (count([RolesSchedule[s1, role] != RolesSchedule[s2, role] | s1, s2 in Students 
              where s1 < s2 /\ 
                    day_func(StartTs[s1]) == day_func(StartTs[s2]) /\
                    StudentRoomSchedule[s1] == StudentRoomSchedule[s2]
           ]) * RolesSoftContinuity[2, role]);

var float: same_degree_in_room = if (SameDegreeInRoom == 0) then 0.0 else
    count([StudentsDegree[s1] != StudentsDegree[s2] | s1, s2 in Students 
              where s1 < s2 /\ 
                    day_func(StartTs[s1]) == day_func(StartTs[s2]) /\
                    StudentRoomSchedule[s1] == StudentRoomSchedule[s2]
           ]) * SameDegreeInRoom 
    endif;

var float: mergeability = max(0.0, if (Mergeability == 0) then 0.0 else
    float(Mergeability) * sum(s in Students)(card(InstructorSchedule[s] union {StudentsSupervisorId[s]}) - TheoryticalMinCard[s] - sum(RolesDemands)) endif);    

var float: obj = 
    supervisor_available + optimal_lunch_len + optimal_start_ts + optimal_finish_ts + 
    minimize_rooms + roles_soft_continuity + same_degree_in_room + mergeability;

solve minimize obj;

% =============================================================================
% 9. OUTPUT
% =============================================================================
output ["StartTs = \(StartTs);\n",
        "StudentRoomSchedule = \(StudentRoomSchedule);\n",
        "InstructorSchedule = \(InstructorSchedule);\n",
        "RolesSchedule = \(RolesSchedule);\n",
        "ExaminersSchedule = \(ExaminersSchedule);\n",
        "LunchStartTs = \(LunchStartTs);\n",
        "LunchLen = \(LunchLen);\n",
        "supervisor_available = \(supervisor_available);\n",
        "optimal_lunch_len = \(optimal_lunch_len);\n",
        "optimal_start_ts = \(optimal_start_ts);\n",
        "optimal_finish_ts = \(optimal_finish_ts);\n",
        "minimize_rooms = \(minimize_rooms);\n",
        "roles_soft_continuity = \(roles_soft_continuity);\n",
        "same_degree_in_room = \(same_degree_in_room);\n",
        "mergeability = \(mergeability);\n",
        "obj = \(obj);"];