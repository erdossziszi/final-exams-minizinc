include "globals.mzn";
int: StudentsNr;    % Number of Students
int: InstructorsNr; % Number of Instructors
int: DaysNr;    % Number of Days
int: SlotsPerDay;   % Exam slots per day for a room
int: AvailabilitySlotsLenght;   % Determines how the number of slots that 1 unit of availability takes up
int: RoomNr;    % Number of rooms
int: ProgrammNr;    % Number of faculty programmes
int: DegreeNr;  % Number of possible degree levels (e.g. BSc, MSc)
int: RolesNr;   % Cardinality of roles
int: CoursesNr; % Number of possible courses to take as an exam
int: LunchTsMinLen; % Minimal number of timeslots for lunch break 

set of int: Instructors = 1..InstructorsNr; % Instructor IDs in a continous set
set of int: Students = 1..StudentsNr;   % Student IDs in a continous set
set of int: Courses = 1..CoursesNr; % Course IDs in a continous set
set of int: Rooms = 1..RoomNr;  % Room IDs in a continous set
set of int: Days = 1..DaysNr;   % Days in a continous set
set of int: Roles = 1..RolesNr; % Role IDs in a continous set
set of int: Programms = 1..ProgrammNr;  % Programme IDs in a continous set

int: TotalTs = DaysNr * SlotsPerDay;    % Total number of Time Slots
int: TotalAvTs = TotalTs div AvailabilitySlotsLenght;   % Number of availabilities per instructor

array[Instructors] of set of 1..ProgrammNr: InstructorsProgramm;    % Set of programmes an instructor is capable of
%array[Instructors, 1..TotalAvTs] of 0..1: InstructorsAvailability;   % Availabilities per instructor (1 = available)
%array[Students,1..TotalAvTs] of 0..1: StudentsAvailability;

int: SessionNr = DaysNr * RoomNr;   % Number of possible exam sessions
set of int: Sessions = 1..SessionNr;    % Exam Session IDs in a continous set

array[Students] of 1..ProgrammNr: StudentsProgramm; % Programme for a given student
array[Students] of 1..DegreeNr: StudentsDegree; % Degree level for a given student
array[Students] of Instructors: StudentsSupervisorId;   % Instructor ID of a given student's supervisor
array[Students] of set of Courses: StudentsCourseIds;   % Courses for a given student

array[Courses] of set of Instructors: CoursesInstructorIds; % Set of instructors a course can be taught by

array[1..(StudentsNr + SessionNr)] of {1}: reqRoom = [1 | _ in 1..(StudentsNr + SessionNr)];    % Array of 1s to run cumulative: all the students + all the lunch times
%--------------------------------------------------------------------------------- hard:
array[Roles] of int: RolesDemands;  % Number of people needed for a given role
array[int] of Roles: RolesContinuity;   % Roles demanding to have the same person per session
/* set of Roles: RolesContinuity;   % Roles demanding to have the same person per session */
array[Programms, Roles] of set of Instructors: InstructorRolesPerProgramm;  % Available instructor for given roles on given programme

array[Days] of set of 1..TotalTs: LunchStarts;  % Lunch break start time slot of a given day

array[Students] of var 1..10: ExamLen;  % Number of time slots needed for a given student's exam

%--------------------------------------------------------------------------------- soft:
int: SupervisorAvailable;
array[1..2] of int: OptimalLunchLenght;
array[1..2] of int: OptimalStartTs;
array[1..2] of int: OptimalFinishTs;
int: MinimizeRooms;
array[1..2,Roles] of int: RolesSoftContinuity;
int: SameDegreeInRoom;
int: Mergeability;
array[Students] of int: TheoryticalMinCard;
%---------------------------------------------------------------------------------

array[Students] of var set of Instructors: InstructorSchedule;  % Instructors scheduled for a given student
array[Students] of var 1..TotalTs: StartTs; % Start time slot for a given student
array[Students] of var set of 1..TotalTs: StudentsTs;   % Time slots for a given student
array[Students] of var Rooms: StudentRoomSchedule; % Room ID for a given student
array[Students, Students] of var 0..1: CollisionMX; % Collision matrix for students - students whose exams happen (somewhat) parallel

array[Students, Roles] of var set of Instructors: RolesSchedule;    % Instructors per roles for a given student
array[Students] of var set of Instructors: ExaminersSchedule;   % Instructors at the exam for a given student


array[Sessions] of var 1..TotalTs: LunchStartTs;    % Starting time slot for the lunch time of a given session
array[Sessions] of var LunchTsMinLen..SlotsPerDay: LunchLen;    % Number of time slots for lunch for a given session
array[Sessions] of var Rooms: SessionRoomSchedule;    %  Room ID for a given session

constraint symmetry_breaking_constraint(
    forall(s1, s2 in Students where ((s1 < s2) /\ (StudentsProgramm[s1] == StudentsProgramm[s2]) /\ (StudentsCourseIds[s1] == StudentsCourseIds[s2]))) (
        StartTs[s1] <= StartTs[s2]
    )
);

% --- Check if the given instructor is in programs and roles ---
function array[Programms, Roles] of bool: check_instructor_in_roles(int: instructor_id) =
  array2d(Programms, Roles, [
    instructor_id in InstructorRolesPerProgramm[p, r] 
    | p in Programms, r in Roles
  ]); 

% Oktató kurzus-kompatibilitása
function set of Courses: check_instructor_courses(int: instructor_id) =
  { c | c in Courses where instructor_id in CoursesInstructorIds[c] };

% =============================================================================
% SZIMMETRIATÖRÉS OKTATÓKRA (Hibrid: Lexikografikus / First-Touch)
% =============================================================================

% --- 1. Segédváltozó az oktatók első megjelenési idejének meghatározására ---
% Ha az oktató sehol sincs beosztva, a maximális idő + 1.0 értéket veszi fel.
array[Instructors] of var 1.0..(TotalTs + 1.0): InstructorFirstStart = [
    min([ if i in InstructorSchedule[s] then StartTs[s] else TotalTs + 1.0 endif | s in Students ])
    | i in Instructors
];

% --- 2. Halmaz azon szerepkörökről, ahol A SOFT CONTINUITY BÜNTETÉS SÚLYA > 0 ---
set of Roles: SoftRoles = { r | r in Roles where RolesSoftContinuity[2, r] > 0 };

% --- 3. Hibrid Szimmetriatörő megkötés ---
constraint symmetry_breaking_constraint(
    forall(i1, i2 in Instructors where (
        (i1 < i2) /\ 
        (check_instructor_in_roles(i1) == check_instructor_in_roles(i2)) /\
        (check_instructor_courses(i1) == check_instructor_courses(i2))
    )) (
        let {
            % Megvizsgáljuk, hogy i1 (és így a vele azonos i2) betölthet-e legalább egy olyan 
            % szerepkört valamelyik szakon, amire él a soft continuity szabály
            bool: is_affected_by_soft_continuity = exists(p in Programms, r in SoftRoles) (
                i1 in InstructorRolesPerProgramm[p, r]
            );
        } in
            if not is_affected_by_soft_continuity then
                % A) Ha NEM érintettek: Marad az eredeti, szigorúbb lexikografikus rendezés
                lex_greatereq([i1 in InstructorSchedule[s] | s in Students], 
                    [i2 in InstructorSchedule[s] | s in Students])
            else
                % B) Ha ÉRINTETTEK: First-Touch szimmetriatörést alkalmazunk
                InstructorFirstStart[i1] <= InstructorFirstStart[i2]
            endif
    )
);


%% Determines what is the day of the time slot
function var int: day(var int: ts, int: unit) =
    ((ts - 1) div unit) + 1;

constraint  %% lunch start time slots in adequate range
    forall(r in Rooms, d in Days) (LunchStartTs[(d - 1) * RoomNr + r] in LunchStarts[d]);

constraint %% time slots of scheduled student exams
    forall(s in Students) (
        StudentsTs[s] == StartTs[s]..(StartTs[s] + ExamLen[s] - 1)
    );

constraint cumulative(StartTs++LunchStartTs, ExamLen++LunchLen, reqRoom, RoomNr);

constraint %% fill in collision matrix: 1 if the time interval for two students intersect
    forall(s1, s2 in Students where s1 < s2) (
        if (StartTs[s1] + ExamLen[s1] <= StartTs[s2] \/ StartTs[s2] + ExamLen[s2] <= StartTs[s1]) 
           then CollisionMX[s1, s2] == 0 
           else CollisionMX[s1, s2] == 1 
        endif
        /\ CollisionMX[s1, s2] == CollisionMX[s2, s1]
    );

constraint %% intersected lunch & exam not in same room - Exam cannot happen in a room with lunch break
    forall(s in Students, L in Sessions) (
        if not (StartTs[s] + ExamLen[s] <= LunchStartTs[L] \/ LunchStartTs[L] + LunchLen[L] <= StartTs[s]) 
           then StudentRoomSchedule[s] != SessionRoomSchedule[L]
        endif
    );

constraint %% lunches in a day in different rooms and increasing order
    forall(d in Days) (strictly_increasing( [ SessionRoomSchedule[(d - 1) * RoomNr + r] | r in Rooms ]) );


constraint %% 1 exam per room: if two exams collide, they are in a different room
    forall(i, j in Students where i < j) (
        if CollisionMX[i, j] == 1 
           then StudentRoomSchedule[i] != StudentRoomSchedule[j]
        endif
    );

constraint %% no exam on 2 days
    forall(s in Students) (
        (StartTs[s] - 1) mod SlotsPerDay <= SlotsPerDay - ExamLen[s]
    );


%constraint %% student & instructor both available at exam time slots
%    forall(s in Students) (
%        forall(ts in StudentsTs[s]) (
%            forall(i in InstructorSchedule[s])(
%                InstructorsAvailability[i, day(ts, AvailabilitySlotsLenght)] == 1
%            )
%        )
%    );
    
constraint %% instructors in Roles matched with programmes, with demands, added to schedule
    forall(s in Students, r in Roles where RolesDemands[r] > 0) (       
        RolesSchedule[s, r] subset InstructorRolesPerProgramm[StudentsProgramm[s], r] /\    % Scheduled instructors for role are in the right programme
        card(RolesSchedule[s, r]) == RolesDemands[r]      % Enough instructors scheduled for role
    );
    
constraint %% instructors in Roles form disjoint sets per exams - Different role means different
    RolesNr > 1 ->  % Only if more than one role
    forall(s in Students, r1, r2 in Roles where r1 < r2) (       
        disjoint(RolesSchedule[s, r1], RolesSchedule[s, r2])
    );

constraint %% We don't schedule for roles demanding less than 1 person
    forall(r in Roles where RolesDemands[r] == 0, s in Students) (
        card(RolesSchedule[s, r]) == 0
    );

constraint %% before/after lunch roles continuity - If role demands continuity, the person is the same until and from lunch break
    length(RolesContinuity) > 0 ->
    forall(s1, s2 in Students where s1 < s2) (  % If two students have exams on the same day in the same room
        let {var int: day_s1 = day(StartTs[s1], SlotsPerDay);} in
        if(day_s1 == day(StartTs[s2], SlotsPerDay))
            then let {var int: room_s1 = StudentRoomSchedule[s1];} in 
                if(room_s1 == StudentRoomSchedule[s2]) 
                    then let {var int: lunch_start = LunchStartTs[(day_s1 - 1) * RoomNr + room_s1]} in
                        if((lunch_start > StartTs[s1]) == (lunch_start > StartTs[s2]))  % Both either before or after lunch
                        then 
                            forall(role in RolesContinuity) (
                                RolesSchedule[s1, role] == RolesSchedule[s2, role] )
                        endif
                endif
            endif
    );


% Scheduling examiners for student

constraint %% no course for a student means no examiners
    forall(s in Students where card(StudentsCourseIds[s]) == 0) (
        card(ExaminersSchedule[s]) == 0
    );

constraint %% examiners, added to schedule
    forall(s in Students where card(StudentsCourseIds[s]) > 0) (
        card(ExaminersSchedule[s]) <= card(StudentsCourseIds[s]) /\
        forall(c in StudentsCourseIds[s]) (
            not disjoint(CoursesInstructorIds[c], ExaminersSchedule[s])
        )
    );

constraint %% no parallel scheduling among instructors
    forall(i, j in Students where i < j) (
        if CollisionMX[i, j] == 1 
           then disjoint(InstructorSchedule[i], InstructorSchedule[j])
        endif
    );

%%%%% -----------------------------------------------------new    
constraint %% instructorschedule valojaban a rolesschedule és examinerschedule unioja
    forall(s in Students) (
        array_union(row(RolesSchedule, s)) union ExaminersSchedule[s] == InstructorSchedule[s]
    );

constraint %% same program in a session
    forall(s1, s2 in Students where s1 < s2)(
        if (StudentRoomSchedule[s1] == StudentRoomSchedule[s2] /\ (day(StartTs[s1], SlotsPerDay) == day(StartTs[s2], SlotsPerDay)))
            then StudentsProgramm[s1] == StudentsProgramm[s2]
        endif
    );

%var int: supervisor_available;
%constraint if (SupervisorAvailable == 0) then supervisor_available == 0 else 
%    supervisor_available == SupervisorAvailable * sum(s in Students, ts in StudentsTs[s]) (
%       (1 - InstructorsAvailability[StudentsSupervisorId[s], day(ts,AvailabilitySlotsLenght)])
%    ) endif;
    
var int: optimal_lunch_len = if (OptimalLunchLenght[1] == 0) then 0 else
    OptimalLunchLenght[1] * sum(L in Sessions)(abs(LunchLen[L] - OptimalLunchLenght[2])) endif;

var int: optimal_start_ts = if (OptimalStartTs[1] == 0) then 0 else
    OptimalStartTs[1] * sum(s in Students where (StartTs[s] - 1) mod SlotsPerDay < OptimalStartTs[2] - 1)
                           (OptimalStartTs[2] - 1 - (StartTs[s] - 1) mod SlotsPerDay) endif;

var int: optimal_finish_ts = if (OptimalFinishTs[1] == 0) then 0 else
    OptimalFinishTs[1] * sum(s in Students where (StartTs[s] + ExamLen[s] - 2) mod SlotsPerDay > OptimalFinishTs[2] - 1)
                            ((StartTs[s] + ExamLen[s] - 2) mod SlotsPerDay - (OptimalFinishTs[2] - 1)) endif;   
    

var int: minimize_rooms = if (MinimizeRooms == 0) then 0 else
    MinimizeRooms * (card(array2set(StudentRoomSchedule)) - day(day(sum(ExamLen),SlotsPerDay),DaysNr)) endif; %tényleges termek - min szükségesek

var int: roles_soft_continuity = 
    sum(role in Roles where RolesSoftContinuity[2,role] > 0)
    (count([RolesSchedule[s1,role] != RolesSchedule[s2,role] | s1, s2 in Students 
              where s1<s2 /\ 
                    day(StartTs[s1],SlotsPerDay) == day(StartTs[s2],SlotsPerDay) /\
                    StudentRoomSchedule[s1] == StudentRoomSchedule[s2]
           ]) * RolesSoftContinuity[2,role]);


var int: same_degree_in_room = if (SameDegreeInRoom == 0) then 0 else
    count([StudentsDegree[s1] != StudentsDegree[s2] | s1, s2 in Students 
              where s1<s2 /\ 
                    day(StartTs[s1],SlotsPerDay) == day(StartTs[s2],SlotsPerDay) /\
                    StudentRoomSchedule[s1] == StudentRoomSchedule[s2]
           ]) * SameDegreeInRoom 
    endif;

var int: mergeability = max(0, if (Mergeability == 0) then 0 else
    Mergeability * sum(s in Students)(card(InstructorSchedule[s] union {StudentsSupervisorId[s]}) - TheoryticalMinCard[s] - sum(RolesDemands)) endif);    
  

var int: obj = 
%supervisor_available + 
optimal_lunch_len + optimal_start_ts + optimal_finish_ts + minimize_rooms + roles_soft_continuity + same_degree_in_room + mergeability;
                                             
solve minimize obj;

output ["StartTs = \(StartTs);\n",
        "StudentRoomSchedule = \(StudentRoomSchedule);\n",
        "InstructorSchedule = \(InstructorSchedule);\n",
        "RolesSchedule = \(RolesSchedule);\n",
        "ExaminersSchedule = \(ExaminersSchedule);\n",
        "LunchStartTs = \(LunchStartTs);\n",
        "LunchLen = \(LunchLen);\n",
 %       "supervisor_available = " ++ show(supervisor_available),
        ";\noptimal_lunch_len = \(optimal_lunch_len);\n",
        "optimal_start_ts = \(optimal_start_ts);\n",
        "optimal_finish_ts = \(optimal_finish_ts);\n",
        "minimize_rooms = \(minimize_rooms);\n",
        "roles_soft_continuity = \(roles_soft_continuity);\n",
        "same_degree_in_room = \(same_degree_in_room);\n",
        "mergeability = \(mergeability);\n",
        "obj = \(obj);"];
