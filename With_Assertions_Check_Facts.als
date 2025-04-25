
one sig NationalHolidays {
  dates: set String
}
abstract sig CaseStatus {}
one sig Open, Closed extends CaseStatus {}

abstract sig Person {
  id: one String,
  name: one String,
  email: one String,
  phoneNumber: one Int,
  dob: one String,
  gender: one String
}

sig Patient extends Person {
  prescription: some Prescription,
  appointment: some Appointment,
  bill: some Bill,
  ehr: one EHR,
  dischargeSummary: lone DischargeSummary,
  bed: lone Bed,
  caseStatus: one CaseStatus
}

sig Staff extends Person {
  type: one String,
  isOnLeave: one Int,
  qualification: some String,
  assignedShifts: set Shift
}

sig Doctor extends Staff {
  maxAppointmentsPerDay: one Int,
  rank: one String,
  appointments: set Appointment
}

sig Appointment {
  id: one String,
  type: one String,
  date: one String,
  status: one String,
  doctor: one Doctor,
  patient: one Patient,
  resources: some Resource,
  labTests: some LabTest,
  remainder: lone Remainder,
  timeSlot: one TimeSlot
}

sig Prescription {
  id: one String,
  medicines: some Medicine,
  appointment: one Appointment
}

sig Bill {
  totalAmount: one Int,
  isPaid: one Int,
  appointment: one Appointment
}

sig LabTest {
  id: one Int,
  appointment: one Appointment,
  testCost: one Int
}

sig EHR {
  id: one Int,
  dateCreated: one String,
  currentMedications: set Medicine,
  pastSurgeries: set Surgery,
  labTests: set LabTest,
  allergies: set Allergy,
  patient: one Patient,
  receivedtreatment: one Int
}

sig Bed {
  id: one Int,
  location: one String,
  isOccupied: one Int,
  assignedPatient: lone Patient,
  type: one String //"General Ward", "ICU", "CCU"
}

sig Surgery {
  id: one Int,
  anesthetist: one Staff,
  assignedOT: one String,
  appointment: one Appointment
}

sig DischargeSummary {
  summaryID: one Int,
  dischargeDate: one String,
  status: one String,
  signedBy: one Doctor,
  patient: one Patient
}

sig Pharmacy {
  medicines: some Medicine
}

sig Medicine {
  id: one String,
  name: one String,
  stock: one Int,
  threshold: one Int,
  allergens: set String,
  medicineCost: one Int
}

sig Allergy {
  allergyID: one String,
  name: one String,
  severity: one String,
  reaction: lone String,
  isClinicallyConfirmed: one Int,
  identificationDate: lone String
}

sig Resource {
  type: one String,
  isAvailable: one Int,
  resourceCost: one Int,
  appointment: one Appointment
}

sig Shift {
  id: one Int,
  date: one String,
  type: one String,  //Doctor, Nurse, QualityAssuranceTeam
  location: one String, 
  startingTime: one Time,
  endingTime: one Time,
  timeSlot: set TimeSlot,
  assignedTo: set Staff
}

sig TimeSlot {
  startingTime: one Time,
  endingTime: one Time
}

// Time.
sig Time {
  hour: one Int,
  minute: one Int
}

sig OperationTheater {
  id: one Int
}

sig Remainder {
  id: one Int,
  sentTime: one Time,
  remainderOfAppointment: one Appointment
}


sig Feedback {
  id: one Int,
  rating: one Int,
  comment: lone String,
  appointment: one Appointment,
  notifiedTeam: set Staff // Relation to staff of type "QualityAssuranceTeam"
}

sig LowStockAlert {
  medicine: one Medicine,
  generatedOn: one String,
  sentTo: one Staff
}


fun timeInMinutes[t: Time]: Int {
  mul[t.hour, 60] + t.minute
}


//<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<Simple Structural>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

// 1. A doctor can be assigned to multiple patients.
fact DoctorCanHaveMultiplePatients {
  all d: Doctor |
    #({ p: Patient | some a: d.appointments | a.patient = p }) > 1
}

// Assertion
assert DoctorCanHaveMultiplePatientsAssertion {
  all d: Doctor |
    #({ p: Patient | some a: d.appointments | a.patient = p }) > 1
}
check DoctorCanHaveMultiplePatientsAssertion for 5

//2. A resource can be assigned to only one patient at a time.
fact EachResourceAssignedToOnePatient {
  all r: Resource |
    one r.appointment.patient
}

// Assertion to ensure no two resources are assigned to the same patient at the same time.
assert ResourceAssignedToOnePatientAssertion {
  all r: Resource |
    one r.appointment.patient
}

check ResourceAssignedToOnePatientAssertion for 5

// 3. Each appointment is linked to one doctor and one patient.
fact EachAppointmentLinkedToDoctorAndPatient {
  all a: Appointment |
    one a.doctor and one a.patient
}

// Assertion.
assert EachAppointmentLinkedToDoctorAndPatient {
  all a: Appointment |
    one a.doctor and one a.patient
}
check EachAppointmentLinkedToDoctorAndPatient for 5

// 4. Each prescription is issued by a registered doctor.
fact PrescriptionsAreIssuedByDoctors {
  all p: Prescription |
    one p.appointment.doctor
}

// Assertion.
assert PrescriptionsAreIssuedByDoctorsAssertion {
  all p: Prescription |
    one p.appointment.doctor
}
check PrescriptionsAreIssuedByDoctorsAssertion for 5

// 5. Every bill corresponds to a single patient.
fact BillLinkedToOnePatient {
  all b: Bill | one b.appointment.patient
}

// Assertion.
assert BillLinkedToOnePatientAssertion {
  all b: Bill |
    one b.appointment.patient
}
check BillLinkedToOnePatientAssertion for 5

//<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<Business or Real World Rules (5 - 10)>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

//Appointments cannot be scheduled on national holidays except in emergencies.
fact NoAppointmentOnNationalHolidaysExceptEmergency{
   all a: Appointment | a.date in NationalHolidays.dates implies a.type = "Emergency"
}

// Assertion.
assert NoAppointmentOnNationalHolidaysExceptEmergencyAssertion {
  all a: Appointment |
    a.date in NationalHolidays.dates implies a.type = "Emergency"
}
check NoAppointmentOnNationalHolidaysExceptEmergencyAssertion for 5
