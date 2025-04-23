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
  bed: lone Bed
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
  appointment: one Appointment
}

sig EHR {
  id: one Int,
  dateCreated: one String,
  currentMedications: set Medicine,
  pastSurgeries: set Surgery,
  labTests: set LabTest,
  allergies: set Allergy,
  patient: one Patient
}

sig Bed {
  id: one Int,
  location: one String,
  isOccupied: one Int,
  assignedPatient: lone Patient
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
  allergens: set String
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
  appointment: one Appointment
}

sig Shift {
  id: one Int,
  date: one String,
  type: one String,
  startingTime: one String,
  endingTime: one String,
  timeSlot: set TimeSlot,
  assignedTo: set Staff
}

sig TimeSlot {
  startingTime: one Time,
  endingTime: one Time
}

sig OperationTheater {
  id: one Int
}

sig Remainder {
  id: one Int,
  remainderOfAppointment: one Appointment
}

sig Feedback {
  id: one Int,
  rating: one Int,
  comment: lone String,
  appointment: one Appointment
}

// Time.
sig Time {
  hour: one Int,
  minute: one Int
}

//Simple Structural:
fact DoctorCanHaveMultiplePatients {
  all d: Doctor |
    #({ p: Patient | some a: d.appointments | a.patient = p }) > 1
}

fact ResourceAssignedToOnePatient {
  all r1, r2: Resource |
    r1 != r2 and r1.appointment.patient != r2.appointment.patient => r1 != r2
}

fact EachAppointmentLinkedToDoctorAndPatient {
  all a: Appointment |
    one a.doctor and one a.patient
}

fact PrescriptionsAreIssuedByDoctors {
  all p: Prescription |
    one p.appointment.doctor
}

fact BillLinkedToOnePatient {
  all b: Bill | one b.appointment.patient
}

// Fact Syntax.
/*
fact NameOfTheFact {
   quantifier variable: Set | expression
   all x: Set | d.maxAppointmentPerDay >= 1
}
*/

fun timeInMinutes[t: Time]: Int {
  mul[t.hour, 60] + t.minute
}

// Complex.
// No two appointments for the same doctor can overlap in time.
fact NoOverlappingAppointments {
  all app1, app2: Appointment |
    app1 != app2 and app1.doctor = app2.doctor =>
      app1.date != app2.date or
      timeInMinutes[app1.timeSlot.endingTime] <= timeInMinutes[app2.timeSlot.startingTime] or
      timeInMinutes[app2.timeSlot.endingTime] <= timeInMinutes[app1.timeSlot.startingTime]
}

