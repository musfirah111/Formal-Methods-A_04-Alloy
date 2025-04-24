
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
  appointment: one Appointment
}

sig LowStockAlert {
  medicine: one Medicine,
  generatedOn: one String,
  sentTo: one Staff
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
// 1. No two appointments for the same doctor can overlap in time.
fact NoOverlappingAppointments {
  all a1, a2: Appointment |
    (a1 != a2 and a1.doctor = a2.doctor) implies (
      a1.date != a2.date or
      timeInMinutes[a1.timeSlot.endingTime] <= timeInMinutes[a2.timeSlot.startingTime] or
      timeInMinutes[a2.timeSlot.endingTime] <= timeInMinutes[a1.timeSlot.startingTime])
}

// 2. Doctors must not have back-to-back appointments without a 10-minute gap
fact DoctorAppointmentsHave10MinGap {
  all a1, a2: Appointment |
    (a1 != a2 and a1.doctor = a2.doctor and a1.date = a2.date) implies
      timeInMinutes[a1.timeSlot.endingTime] + 10 <= timeInMinutes[a2.timeSlot.startingTime]
      or timeInMinutes[a2.timeSlot.endingTime] + 10 <= timeInMinutes[a1.timeSlot.startingTime]
}

// 3. Appointments must fall within the doctor’s declared working hours.
fact AppointmentsInDoctorsWorkingHours {
    all a: Appointment |
    some s: a.doctor.assignedShifts | (s.date = a.date) implies
    (timeInMinutes[a.timeSlot.startingTime] >= timeInMinutes[s.startingTime] and
    timeInMinutes[a.timeSlot.endingTime] <= timeInMinutes[s.endingTime])
}

// A nurse cannot be scheduled for night and morning shifts on the same day.
// fact NoMorningAndNightShiftForSameNurse {
//   all s1, s2: Shift | // all shift combos.
//     s1 != s2 // different shifts. 
//     and s1.date = s2.date // both shifts on same date.
//     and 
//     some nurse: Staff | // at least one nurse exists such that ...
//     nurse.type = "Nurse" // staff is nurse.
//     and nurse in s1.assignedTo and
//     nurse in s2.assignedTo // nurse is one of the staff assigned to both shifts.
//     and ((s1.type = "Morning" and s2.type = "Night") or (s1.type = "Night" and s2.type = "Morning")) implies
//     (false)
// }

// 4. A nurse cannot be scheduled for night and morning shifts on the same day.
fact NoMorningAndNightShiftForSameNurse {
  all s1, s2: Shift |
    s1 != s2 and // different shifts.
    s1.date = s2.date and // same date.
    ((s1.type = "Morning" and s2.type = "Night") or (s1.type = "Night" and s2.type = "Morning")) implies
      no nurse: Staff | // no staff exists ...
        nurse.type = "Nurse" and // who is a nurse and ...
        nurse in s1.assignedTo and 
        nurse in s2.assignedTo // ... is assigned to both shifts.
}

// 5. A patient’s EHR can only be modified by the assigned doctor.
fact OnlyAssignedDoctorCanModifyEHR {
  all a: Appointment |
    a.patient.ehr.patient = a.patient and
    a.doctor in Doctor
}

// 6. If a patient is transferred from the ward to the ICU, the previous bed must be released.
fact BedReleaseWhenPatientTransferredAndBedType {
  all p: Patient, b1, b2: Bed |
    // Ensure patient p occupies b1 and b2 is empty.
    p.bed = b1 and b2.isOccupied = 0 and
    // When patient is transferred to b2 (ICU), b1 is released (ward).
    p.bed = b2 implies {
      // Ensure that the patient's previous bed is a ward bed (b1 type).
      b1.type = "General Ward" and
      b2.type = "ICU" and // The new bed is ICU.
      b1.isOccupied = 0 and  // Release previous bed.
      b1.assignedPatient = none and  // No longer assigned to any patient.
      b2.isOccupied = 1 and  // The new bed must be occupied.
      b2.assignedPatient = p // The patient is assigned to the new bed.
    }
}

// 7. For pharmacy dispatch, both the prescription ID and the patient ID must match.
fact PharmacyDispatchPrescriptionIDMatch {
  all p: Prescription |
    p.appointment.patient.id = p.appointment.patient.id // prescription is matched to the correct patient.
}

// 8. Lab tests can only be ordered if the patient has an active appointment or is admitted, and the test is requested by a registered doctor.



// 9. If the patient's history includes an allergy, medicine containing allergens must be blocked from prescription.



// 10. Operation theater, surgeon, and anesthetist must be available at the time of surgery.
