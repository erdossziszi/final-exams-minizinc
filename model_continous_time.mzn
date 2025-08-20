include "globals.mzn";
int: StudentsNr;    % Number of Students
int: InstructorsNr; % Number of Instructors
int: DaysNr;    % Number of Days
int: SlotsPerDay;   % Lenght of a day for a room
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

int: TotalPeriod = DaysNr * SlotsPerDay;    % Total lenght of the examination period
int: TotalAvTs = TotalPeriod div AvailabilitySlotsLenght;   % Number of availabilities per instructor

array[Instructors] of set of 1..ProgrammNr: InstructorsProgramm;    % Set of programmes an instructor is capable of
array[Instructors, 1..TotalAvTs] of 0..1: InstructorsAvailability;   % Availabilities per instructor (1 = available)
%array[Students,1..TotalAvTs] of 0..1: StudentsAvailability; % ???????????????????????????????????????????????????????????????????????????

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

array[Days] of set of 0..TotalPeriod: LunchStarts;  % Lunch break start time slot of a given day

array[Students] of 1..10: ExamLen;  % Number of time slots needed for a given student's exam

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
array[Students] of var 0.0..TotalPeriod: StartTime; % Start time for a given student
array[Students] of var 0.0..TotalPeriod: EndTime;   % End time for a given student
array[Students] of var Rooms: StudentRoomSchedule; % Room ID for a given student
array[Students, Students] of var 0..1: CollisionMX; % Collision matrix for students - students whose exams happen (somewhat) parallel

array[Students, Roles] of var set of Instructors: RolesSchedule;    % Instructors per roles for a given student
array[Students] of var set of Instructors: ExaminersSchedule;   % Instructors at the exam for a given student


array[Sessions] of var 0.0..TotalPeriod: LunchStart;    % Starting time for the lunch time of a given session
array[Sessions] of var int2float(LunchTsMinLen)..int2float(SlotsPerDay): LunchLen;    % Number of time slots for lunch for a given session
array[Sessions] of var Rooms: SessionRoomSchedule;    %  Room ID for a given session

float: ExamLenTolerance = min(ExamLen) / 10.0; % Tolerance of the length of the exams

% constraint symmetry_breaking_constraint(
%     forall(s1, s2 in Students where ((s1 < s2) /\ (StudentsProgramm[s1] == StudentsProgramm[s2]) /\ (StudentsCourseIds[s1] == StudentsCourseIds[s2]))) (
%         StartTime[s1] <= StartTime[s2]
%     )
% ); 

%% Determines what is the day of the time 
function var int: day(var float: time, int: unit) =
    round(time) div unit;

constraint  %% lunch start time slots in adequate range
    forall(r in Rooms, d in Days) (
        LunchStart[(d - 1) * RoomNr + r] >= min(LunchStarts[d]) /\ LunchStart[(d - 1) * RoomNr + r] <= max(LunchStarts[d])
        );

constraint %% time slots of scheduled student exams
    forall(s in Students) (
        EndTime[s] - StartTime[s] >= ExamLen[s] - 0.5 /\
        EndTime[s] - StartTime[s] <= ExamLen[s] + 0.5
    );

%constraint cumulative(StartTs++LunchStartTs, ExamLen++LunchLen, reqRoom, RoomNr);

constraint %% fill in collision matrix: 1 if the time interval for two students intersect
    forall(s1, s2 in Students where s1 < s2) (
        if (StartTime[s1] + ExamLen[s1] <= StartTime[s2] \/ StartTime[s2] + ExamLen[s2] <= StartTime[s1]) 
           then CollisionMX[s1, s2] == 0 
           else CollisionMX[s1, s2] == 1 
        endif
        /\ CollisionMX[s1, s2] == CollisionMX[s2, s1]
    );

%%--------------------------- rossz
% constraint
%    forall(i in Students) (
%       sum(j in Students) (CollisionMX[i, j]) <= RoomNr
%    );

constraint %% intersected lunch & exam not in same room - Exam cannot happen in a room with lunch break
    forall(s in Students, L in Sessions) (
        if not (StartTime[s] + ExamLen[s] <= LunchStart[L] \/ LunchStart[L] + LunchLen[L] <= StartTime[s]) 
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
        round(StartTime[s]) div SlotsPerDay == round(EndTime[s]) div SlotsPerDay
    );


constraint %% student & instructor both available at exam time slots
    forall(s in Students) (
        forall(ts in (floor(StartTime[s] - 0.001) div AvailabilitySlotsLenght + 1)..(floor(EndTime[s] - 0.001) div AvailabilitySlotsLenght + 1)) (
            forall(i in InstructorSchedule[s]) (
                InstructorsAvailability[i, ts] == 1
            )
        )
    );
    
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
        let {var int: day_s1 = day(StartTime[s1], SlotsPerDay);} in
        if(day_s1 == day(StartTime[s2], SlotsPerDay))
            then let {var int: room_s1 = StudentRoomSchedule[s1];} in 
                if(room_s1 == StudentRoomSchedule[s2]) 
                    then let {var float: lunch_start = LunchStart[(day_s1 - 1) * RoomNr + room_s1]} in
                        if((lunch_start > StartTime[s1]) == (lunch_start > StartTime[s2]))  % Both either before or after lunch
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
    forall(s in Students, r in Roles) (
        array_union(row(RolesSchedule, s)) union ExaminersSchedule[s] == InstructorSchedule[s]
    );

constraint %% same program in a session
    forall(s1, s2 in Students where s1 < s2)(
        if (StudentRoomSchedule[s1] == StudentRoomSchedule[s2] /\ (day(StartTime[s1], SlotsPerDay) == day(StartTime[s2], SlotsPerDay)))
            then StudentsProgramm[s1] == StudentsProgramm[s2]
        endif
    );

var int: supervisor_available = if (SupervisorAvailable == 0) then 0 else 
    SupervisorAvailable * sum(s in Students, ts in (floor(StartTime[s] - 0.001) div AvailabilitySlotsLenght + 1)..(floor(EndTime[s] - 0.001) div AvailabilitySlotsLenght + 1)) (
       1 - InstructorsAvailability[StudentsSupervisorId[s], ts]
    ) endif;

var int: optimal_lunch_len = if (OptimalLunchLenght[1] == 0) then 0 else
    OptimalLunchLenght[1] * sum(L in Sessions)(abs(round(LunchLen[L]) - OptimalLunchLenght[2])) endif;

var int: optimal_start_ts = if (OptimalStartTs[1] == 0) then 0 else
    OptimalStartTs[1] * sum(s in Students where round(StartTime[s]) mod SlotsPerDay < OptimalStartTs[2])
                           (OptimalStartTs[2] - round(StartTime[s]) mod SlotsPerDay) endif;

var int: optimal_finish_ts = if (OptimalFinishTs[1] == 0) then 0 else
    OptimalFinishTs[1] * sum(s in Students where round(EndTime[s]) mod SlotsPerDay > OptimalFinishTs[2])
                            (round(EndTime[s]) mod SlotsPerDay - OptimalFinishTs[2]) endif;   
    
var int: minimize_rooms = if (MinimizeRooms == 0) then 0 else
    MinimizeRooms * (card(array2set(StudentRoomSchedule)) - (sum(ExamLen) div SlotsPerDay) div DaysNr - 1) endif; %tényleges termek - min szükségesek

var int: roles_soft_continuity = 
    sum(role in Roles where RolesSoftContinuity[2,role] > 0)
    (count([RolesSchedule[s1,role] != RolesSchedule[s2,role] | s1, s2 in Students 
              where s1 < s2 /\ 
                    day(StartTime[s1], SlotsPerDay) == day(StartTime[s2], SlotsPerDay) /\
                    StudentRoomSchedule[s1] == StudentRoomSchedule[s2]
           ]) * RolesSoftContinuity[2,role]);

var int: same_degree_in_room = if (SameDegreeInRoom == 0) then 0 else
    count([StudentsDegree[s1] != StudentsDegree[s2] | s1, s2 in Students 
              where s1 < s2 /\ 
                    day(StartTime[s1], SlotsPerDay) == day(StartTime[s2], SlotsPerDay) /\
                    StudentRoomSchedule[s1] == StudentRoomSchedule[s2]
           ]) * SameDegreeInRoom 
    endif;

var int: mergeability = max(0, if (Mergeability == 0) then 0 else
    Mergeability * sum(s in Students)(card(InstructorSchedule[s] union {StudentsSupervisorId[s]}) - TheoryticalMinCard[s] - sum(RolesDemands)) endif);    
  
var int: obj = supervisor_available + optimal_lunch_len + optimal_start_ts + optimal_finish_ts + minimize_rooms + roles_soft_continuity + same_degree_in_room + mergeability;
                                             
solve minimize obj;

output ["StartTime = \(StartTime);\n",
        "EndTime = \(EndTime);\n",
        "StudentRoomSchedule = \(StudentRoomSchedule);\n",
        "InstructorSchedule = \(InstructorSchedule);\n",
        "RolesSchedule = \(RolesSchedule);\n",
        "ExaminersSchedule = \(ExaminersSchedule);\n",
        "LunchStartTs = \(LunchStart);\n",
        "LunchLen = \(LunchLen);\n",
        "RoomNr = \(RoomNr);\n",
        "DaysNr = \(DaysNr);\n",
        "SlotsPerDay = \(SlotsPerDay);\n",
        "supervisor_available = " ++ show(supervisor_available),
        ";\noptimal_lunch_len = \(optimal_lunch_len);\n",
        "optimal_start_ts = \(optimal_start_ts);\n",
        "optimal_finish_ts = \(optimal_finish_ts);\n",
        "minimize_rooms = \(minimize_rooms);\n",
        "roles_soft_continuity = \(roles_soft_continuity);\n",
        "same_degree_in_room = \(same_degree_in_room);\n",
        "mergeability = \(mergeability);\n",
        "obj = \(obj);"];
